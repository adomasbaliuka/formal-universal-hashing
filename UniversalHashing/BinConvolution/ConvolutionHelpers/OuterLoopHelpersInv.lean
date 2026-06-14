/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib
import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpers
import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpersInverseNTT


/-!
# Inverse NTT outer-loop correctness

This file contains the heavy inverse-pass outer-loop lemmas, split out from `OuterLoopHelpers`
to keep per-file elaboration memory bounded.  The lightweight inverse infrastructure
(`outerLoop_inv_inverse`, `ntt_sub_input_inv`, the `_gen` structural lemmas, `twiddle_inv_exp`,
and the `ntt_sub_input_inv_block_*` lemmas) lives in `OuterLoopHelpers`.
-/

/-- Split a full `radix4Inner` pass at index `j2nat` into: leading `j2nat` steps,
    one butterfly at `j2nat`, then trailing steps. -/
private lemma radix4Inner_split_at {m : ℕ} (inv : Bool)
    (roots a : Vector UInt32 m) (s_nat len_nat i2_nat j2nat : ℕ)
    (hs_split : s_nat = j2nat + (1 + (s_nat - j2nat - 1))) :
    radix4Inner inv roots s_nat len_nat i2_nat s_nat 0 a =
    radix4Inner inv roots s_nat len_nat i2_nat (s_nat - j2nat - 1) (j2nat + 1)
      (butterfly4 (radix4Inner inv roots s_nat len_nat i2_nat j2nat 0 a)
        inv roots s_nat len_nat i2_nat j2nat) := by
  conv_lhs => rw [hs_split, radix4Inner_comp]
  rw [(by omega : (0 : ℕ) + j2nat = j2nat), radix4Inner_comp]
  have h_inner : radix4Inner inv roots s_nat len_nat i2_nat 1 j2nat
      (radix4Inner inv roots s_nat len_nat i2_nat j2nat 0 a) =
      butterfly4 (radix4Inner inv roots s_nat len_nat i2_nat j2nat 0 a)
        inv roots s_nat len_nat i2_nat j2nat := by
    simp only [radix4Inner]
  simp only [← hs_split]
  rw [h_inner]

/-- The three inverse-NTT twiddle factor identities for a block at level `q`. -/
private lemma inv_twiddle_eqs (q j2nat : ℕ) (hj2_lt : j2nat < 2 ^ q)
    (h_dvd_q1 : 2 ^ (q + 1) ∣ mod64.toNat - 1)
    (h_dvd_q2 : 2 ^ (q + 2) ∣ mod64.toNat - 1)
    (ω_top : ZMod mod32.toNat)
    (hω_top : ω_top =
      ((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ (q + 2)))⁻¹) :
    (primRoot.toNat : ZMod mod32.toNat) ^
        ((mod64.toNat - 1) / 2 ^ (q + 1) * (2 ^ (q + 1) - j2nat)) = (ω_top ^ 2) ^ j2nat
    ∧ (primRoot.toNat : ZMod mod32.toNat) ^
        ((mod64.toNat - 1) / 2 ^ (q + 2) * (2 ^ (q + 2) - j2nat)) = ω_top ^ j2nat
    ∧ (primRoot.toNat : ZMod mod32.toNat) ^
        ((mod64.toNat - 1) / 2 ^ (q + 2) * (2 ^ (q + 2) - 2 ^ q - j2nat)) =
        ω_top ^ (2 ^ q + j2nat) := by
  subst hω_top
  have hj2_le_q2 : j2nat ≤ 2 ^ (q + 2) :=
    le_of_lt (lt_of_lt_of_le hj2_lt (Nat.pow_le_pow_right (by decide) (by omega)))
  have hj2_le_q1 : j2nat ≤ 2 ^ (q + 1) :=
    le_of_lt (lt_of_lt_of_le hj2_lt (Nat.pow_le_pow_right (by decide) (by omega)))
  have hsum_le : 2 ^ q + j2nat ≤ 2 ^ (q + 2) := by
    have : 2 ^ q + 2 ^ q ≤ 2 ^ (q + 2) := by
      rw [(by ring : 2 ^ (q + 2) = 2 ^ q + (2 ^ q + 2 ^ q + 2 ^ q))]; omega
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [twiddle_inv_exp (2 ^ (q + 1)) j2nat h_dvd_q1 hj2_le_q1 (Nat.two_pow_pos _)]
    congr 1; rw [inv_pow, ← pow_mul]; congr 2
    obtain ⟨K, hK⟩ := h_dvd_q2
    have hpos : (2 : ℕ) ^ (q + 2) > 0 := Nat.two_pow_pos _
    have hpos1 : (2 : ℕ) ^ (q + 1) > 0 := Nat.two_pow_pos _
    rw [hK, Nat.mul_div_cancel_left _ hpos, (by ring : (2 : ℕ) ^ (q + 2) = 2 * 2 ^ (q + 1)),
        (by ring : 2 * 2 ^ (q + 1) * K = 2 ^ (q + 1) * (2 * K)),
        Nat.mul_div_cancel_left _ hpos1]; ring
  · exact twiddle_inv_exp (2 ^ (q + 2)) j2nat h_dvd_q2 hj2_le_q2 (Nat.two_pow_pos _)
  · rw [(by omega : 2 ^ (q + 2) - 2 ^ q - j2nat = 2 ^ (q + 2) - (2 ^ q + j2nat))]
    exact twiddle_inv_exp (2 ^ (q + 2)) (2 ^ q + j2nat) h_dvd_q2 hsum_le (Nat.two_pow_pos _)

private lemma block_idx_lt (q b k j2nat n : ℕ) (hk : k < 4)
    (hb : b < 2 ^ (n - q - 2)) (hj2 : j2nat < 2 ^ q) (hq : q + 2 ≤ n) :
    (4 * b + k) * 2 ^ q + j2nat < 2 ^ n := by
  have h_lt_bp1 : (4 * b + k) * 2 ^ q + j2nat < (b + 1) * 2 ^ (q + 2) := by
    have hk3 : k ≤ 3 := by omega
    nlinarith [(by ring : 2 ^ (q + 2) = 4 * 2 ^ q), Nat.two_pow_pos q]
  calc (4 * b + k) * 2 ^ q + j2nat
      < (b + 1) * 2 ^ (q + 2) := h_lt_bp1
    _ ≤ 2 ^ (n - q - 2) * 2 ^ (q + 2) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ n := by rw [← pow_add]; congr 1; omega

/-- Proves the four-way case split on `quad` for the inverse NTT block correctness.
    Isolated so that `interval_cases` runs in a small context. -/
private lemma radix4InnerInv_case_split {m : ℕ} (q b : ℕ) (r : Fin (2 ^ (q + 2)))
    (j2nat quad : ℕ) (hp : Fact (Nat.Prime mod32.toNat))
    (hj2_lt : j2nat < 2 ^ q) (hquad_lt : quad < 4)
    (hr_decomp : r.val = quad * 2 ^ q + j2nat)
    (hidx : b * 2 ^ (q + 2) + r.val < m)
    (i2 j2u s len : UInt64)
    (ω_top : ZMod mod32.toNat)
    (f_ntt : Fin (2 ^ (q + 2)) → ZMod mod32.toNat)
    (A_lead roots : Vector UInt32 m) (a : Vector UInt32 m)
    (hbnd0 : (i2 + j2u).toNat < m)
    (hbnd1 : (i2 + j2u + s).toNat < m)
    (hbnd2 : (i2 + len + j2u).toNat < m)
    (hbnd3 : (i2 + len + j2u + s).toNat < m)
    (hbnd0_nat : i2.toNat + j2u.toNat < m)
    (hbnd1_nat : i2.toNat + j2u.toNat + s.toNat < m)
    (hbnd2_nat : i2.toNat + len.toNat + j2u.toNat < m)
    (hbnd3_nat : i2.toNat + len.toNat + j2u.toNat + s.toNat < m)
    (h_i2_j2_toNat : (i2 + j2u).toNat = b * 2 ^ (q + 2) + j2nat)
    (h_i2_j2_s_toNat : (i2 + j2u + s).toNat = b * 2 ^ (q + 2) + j2nat + 2 ^ q)
    (h_i2_len_j2_toNat : (i2 + len + j2u).toNat = b * 2 ^ (q + 2) + j2nat + 2 ^ (q + 1))
    (h_i2_len_j2_s_toNat :
        (i2 + len + j2u + s).toNat = b * 2 ^ (q + 2) + j2nat + 2 ^ (q + 1) + 2 ^ q)
    (hj2u_toNat : j2u.toNat = j2nat)
    (h_add0 : (i2 + j2u).toNat = i2.toNat + j2u.toNat)
    (h_add1 : (i2 + j2u + s).toNat = i2.toNat + j2u.toNat + s.toNat)
    (h_add2 : (i2 + len + j2u).toNat = i2.toNat + len.toNat + j2u.toNat)
    (h_add3 : (i2 + len + j2u + s).toNat = i2.toNat + len.toNat + j2u.toNat + s.toNat)
    (h_split :
        radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat 0 a =
        radix4Inner true roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1) (j2nat + 1)
          (butterfly4 A_lead true roots s.toNat len.toNat i2.toNat j2nat))
    (h_trailing_pos0 : ∀ B : Vector UInt32 m,
        (radix4Inner true roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
            (j2nat + 1) B)[(i2 + j2u).toNat]'hbnd0 = B[(i2 + j2u).toNat]'hbnd0)
    (h_trailing_pos1 : ∀ B : Vector UInt32 m,
        (radix4Inner true roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
            (j2nat + 1) B)[(i2 + j2u + s).toNat]'hbnd1 = B[(i2 + j2u + s).toNat]'hbnd1)
    (h_trailing_pos2 : ∀ B : Vector UInt32 m,
        (radix4Inner true roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
            (j2nat + 1) B)[(i2 + len + j2u).toNat]'hbnd2 = B[(i2 + len + j2u).toNat]'hbnd2)
    (h_trailing_pos3 : ∀ B : Vector UInt32 m,
        (radix4Inner true roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
            (j2nat + 1) B)[(i2 + len + j2u + s).toNat]'hbnd3 =
            B[(i2 + len + j2u + s).toNat]'hbnd3)
    (hbf0 : (((butterfly4 A_lead true roots s.toNat len.toNat i2.toNat
                  j2u.toNat)[i2.toNat + j2u.toNat]'hbnd0_nat).toNat : ZMod mod32.toNat) =
        ref_ntt q (ω_top ^ 4)
            (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val, fin_4mul_lt q j⟩)
            ⟨j2nat, hj2_lt⟩ +
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / len.toNat * (len.toNat - j2u.toNat)) *
            ref_ntt q (ω_top ^ 4)
              (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 2, fin_4mul2_lt q j⟩)
              ⟨j2nat, hj2_lt⟩ +
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / (2 * len.toNat) * (2 * len.toNat - j2u.toNat)) *
            (ref_ntt q (ω_top ^ 4)
                (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 1, fin_4mul1_lt q j⟩)
                ⟨j2nat, hj2_lt⟩ +
              (primRoot.toNat : ZMod mod32.toNat) ^
                  ((mod64.toNat - 1) / len.toNat * (len.toNat - j2u.toNat)) *
                ref_ntt q (ω_top ^ 4)
                  (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 3, fin_4mul3_lt q j⟩)
                  ⟨j2nat, hj2_lt⟩))
    (hbf1 : (((butterfly4 A_lead true roots s.toNat len.toNat i2.toNat
                  j2u.toNat)[i2.toNat + j2u.toNat + s.toNat]'hbnd1_nat).toNat :
                ZMod mod32.toNat) =
        ref_ntt q (ω_top ^ 4)
            (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val, fin_4mul_lt q j⟩)
            ⟨j2nat, hj2_lt⟩ -
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / len.toNat * (len.toNat - j2u.toNat)) *
            ref_ntt q (ω_top ^ 4)
              (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 2, fin_4mul2_lt q j⟩)
              ⟨j2nat, hj2_lt⟩ +
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / (2 * len.toNat) *
                (2 * len.toNat - s.toNat - j2u.toNat)) *
            (ref_ntt q (ω_top ^ 4)
                (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 1, fin_4mul1_lt q j⟩)
                ⟨j2nat, hj2_lt⟩ -
              (primRoot.toNat : ZMod mod32.toNat) ^
                  ((mod64.toNat - 1) / len.toNat * (len.toNat - j2u.toNat)) *
                ref_ntt q (ω_top ^ 4)
                  (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 3, fin_4mul3_lt q j⟩)
                  ⟨j2nat, hj2_lt⟩))
    (hbf2 : (((butterfly4 A_lead true roots s.toNat len.toNat i2.toNat
                  j2u.toNat)[i2.toNat + len.toNat + j2u.toNat]'hbnd2_nat).toNat :
                ZMod mod32.toNat) =
        ref_ntt q (ω_top ^ 4)
            (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val, fin_4mul_lt q j⟩)
            ⟨j2nat, hj2_lt⟩ +
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / len.toNat * (len.toNat - j2u.toNat)) *
            ref_ntt q (ω_top ^ 4)
              (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 2, fin_4mul2_lt q j⟩)
              ⟨j2nat, hj2_lt⟩ -
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / (2 * len.toNat) * (2 * len.toNat - j2u.toNat)) *
            (ref_ntt q (ω_top ^ 4)
                (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 1, fin_4mul1_lt q j⟩)
                ⟨j2nat, hj2_lt⟩ +
              (primRoot.toNat : ZMod mod32.toNat) ^
                  ((mod64.toNat - 1) / len.toNat * (len.toNat - j2u.toNat)) *
                ref_ntt q (ω_top ^ 4)
                  (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 3, fin_4mul3_lt q j⟩)
                  ⟨j2nat, hj2_lt⟩))
    (hbf3 : (((butterfly4 A_lead true roots s.toNat len.toNat i2.toNat
                  j2u.toNat)[i2.toNat + len.toNat + j2u.toNat + s.toNat]'hbnd3_nat).toNat :
                ZMod mod32.toNat) =
        ref_ntt q (ω_top ^ 4)
            (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val, fin_4mul_lt q j⟩)
            ⟨j2nat, hj2_lt⟩ -
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / len.toNat * (len.toNat - j2u.toNat)) *
            ref_ntt q (ω_top ^ 4)
              (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 2, fin_4mul2_lt q j⟩)
              ⟨j2nat, hj2_lt⟩ -
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / (2 * len.toNat) *
                (2 * len.toNat - s.toNat - j2u.toNat)) *
            (ref_ntt q (ω_top ^ 4)
                (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 1, fin_4mul1_lt q j⟩)
                ⟨j2nat, hj2_lt⟩ -
              (primRoot.toNat : ZMod mod32.toNat) ^
                  ((mod64.toNat - 1) / len.toNat * (len.toNat - j2u.toNat)) *
                ref_ntt q (ω_top ^ 4)
                  (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 3, fin_4mul3_lt q j⟩)
                  ⟨j2nat, hj2_lt⟩))
    (h_tau1 : (primRoot.toNat : ZMod mod32.toNat) ^
        ((mod64.toNat - 1) / len.toNat * (len.toNat - j2u.toNat)) = (ω_top ^ 2) ^ j2nat)
    (h_tau2 : (primRoot.toNat : ZMod mod32.toNat) ^
        ((mod64.toNat - 1) / (2 * len.toNat) * (2 * len.toNat - j2u.toNat)) = ω_top ^ j2nat)
    (h_tau3 : (primRoot.toNat : ZMod mod32.toNat) ^
        ((mod64.toNat - 1) / (2 * len.toNat) * (2 * len.toNat - s.toNat - j2u.toNat)) =
        ω_top ^ (2 ^ q + j2nat)) :
    ((radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat
          0 a)[b * 2 ^ (q + 2) + r.val]'hidx).toNat =
      ref_ntt (q + 2) ω_top f_ntt r := by
  haveI := hp
  interval_cases quad
  · -- quad = 0: position is (i2 + j2u).toNat = b*2^(q+2) + j2nat
    have hidx_eq : b * 2 ^ (q + 2) + r.val = (i2 + j2u).toNat := by
      rw [h_i2_j2_toNat, hr_decomp]; ring
    have hsplit_idx :
        (radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat
            0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
        (butterfly4 A_lead true roots s.toNat len.toNat i2.toNat
            j2u.toNat)[i2.toNat + j2u.toNat]'hbnd0_nat := by
      have h1 : (radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
          (radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[(i2 + j2u).toNat]'hbnd0 := getElem_congr_idx hidx_eq
      rw [h1, h_split, h_trailing_pos0, ← hj2u_toNat, getElem_congr_idx h_add0]
    rw [hsplit_idx, hbf0, h_tau1, h_tau2]
    have hr_eq : r = ⟨j2nat, pow2q_lt_q2 q j2nat hj2_lt⟩ :=
      Fin.ext (hr_decomp.trans (by ring))
    rw [hr_eq, ref_ntt_radix4_q0]
  · -- quad = 1: position is (i2 + j2u + s).toNat
    have hidx_eq : b * 2 ^ (q + 2) + r.val = (i2 + j2u + s).toNat := by
      rw [h_i2_j2_s_toNat, hr_decomp]; ring
    have hsplit_idx :
        (radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat
            0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
        (butterfly4 A_lead true roots s.toNat len.toNat i2.toNat
            j2u.toNat)[i2.toNat + j2u.toNat + s.toNat]'hbnd1_nat := by
      have h1 : (radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
          (radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[(i2 + j2u + s).toNat]'hbnd1 := getElem_congr_idx hidx_eq
      rw [h1, h_split, h_trailing_pos1, ← hj2u_toNat, getElem_congr_idx h_add1]
    rw [hsplit_idx, hbf1, h_tau1, h_tau3]
    have hr_eq : r = ⟨j2nat + 2 ^ q, pow2q_add_q_lt_q2 q j2nat hj2_lt⟩ :=
      Fin.ext (hr_decomp.trans (by ring))
    rw [hr_eq, ref_ntt_radix4_q1 q ω_top _ j2nat hj2_lt,
        show (2 : ℕ) ^ q + j2nat = j2nat + 2 ^ q from Nat.add_comm _ _]
  · -- quad = 2: position is (i2 + len + j2u).toNat
    have hidx_eq : b * 2 ^ (q + 2) + r.val = (i2 + len + j2u).toNat := by
      rw [h_i2_len_j2_toNat, hr_decomp]; ring
    have hsplit_idx :
        (radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat
            0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
        (butterfly4 A_lead true roots s.toNat len.toNat i2.toNat
            j2u.toNat)[i2.toNat + len.toNat + j2u.toNat]'hbnd2_nat := by
      have h1 : (radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
          (radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[(i2 + len + j2u).toNat]'hbnd2 := getElem_congr_idx hidx_eq
      rw [h1, h_split, h_trailing_pos2, ← hj2u_toNat, getElem_congr_idx h_add2]
    rw [hsplit_idx, hbf2, h_tau1, h_tau2]
    have hr_eq : r = ⟨j2nat + 2 ^ (q + 1), pow2q_add_q1_lt_q2 q j2nat hj2_lt⟩ :=
      Fin.ext (hr_decomp.trans (by ring))
    rw [hr_eq, ref_ntt_radix4_q2]
  · -- quad = 3: position is (i2 + len + j2u + s).toNat
    have hidx_eq : b * 2 ^ (q + 2) + r.val = (i2 + len + j2u + s).toNat := by
      rw [h_i2_len_j2_s_toNat, hr_decomp]; ring
    have hsplit_idx :
        (radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat
            0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
        (butterfly4 A_lead true roots s.toNat len.toNat i2.toNat
            j2u.toNat)[i2.toNat + len.toNat + j2u.toNat + s.toNat]'hbnd3_nat := by
      have h1 : (radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
          (radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[(i2 + len + j2u + s).toNat]'hbnd3 := getElem_congr_idx hidx_eq
      rw [h1, h_split, h_trailing_pos3, ← hj2u_toNat, getElem_congr_idx h_add3]
    rw [hsplit_idx, hbf3, h_tau1, h_tau3]
    have hr_eq : r = ⟨j2nat + 2 ^ q + 2 ^ (q + 1), pow2q_add_q_q1_lt_q2 q j2nat hj2_lt⟩ :=
      Fin.ext (hr_decomp.trans (by ring))
    rw [hr_eq, ref_ntt_radix4_q3 q ω_top _ j2nat hj2_lt,
        show (2 : ℕ) ^ q + j2nat = j2nat + 2 ^ q from Nat.add_comm _ _]

lemma radix4Inner_single_block_correct_inv {m : ℕ} (n q : ℕ) (hq2 : q + 2 ≤ n)
    (hm_eq : m = 2 ^ n)
    (v : Vector UInt32 m)
    (roots : Vector UInt32 m)
    (hroots : ntt_roots_correct m roots)
    (hroots_bnd : roots.all (· < mod32))
    (h_dvd : 2 ^ n ∣ mod64.toNat - 1)
    (hm_dvd : m ∣ mod64.toNat - 1)
    (a : Vector UInt32 m)
    (ha_bnd : a.all (· < mod32))
    (len : UInt64) (hlen : len.toNat = 2 ^ (q + 1))
    (b : ℕ) (hb : b < 2 ^ (n - (q + 2)))
    (h_inv_k : ∀ k, k < 4 → ∀ (j2 : Fin (2 ^ q))
        (hidx_k : (4 * b + k) * 2 ^ q + j2.val < m),
        ((a[(4 * b + k) * 2 ^ q + j2.val]'hidx_k).toNat : ZMod mod32.toNat) =
          ref_ntt q
            (((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ q))⁻¹)
            (ntt_sub_input_inv n q (by omega) hm_eq v (4 * b + k)) j2)
    (r : Fin (2 ^ (q + 2)))
    (hidx : b * 2 ^ (q + 2) + r.val < m) :
    let s := len >>> 1
    let i2 := (b * 2 * len.toNat).toUInt64
    ((radix4Inner true roots s.toNat len.toNat i2.toNat s.toNat
        0 a)[b * 2 ^ (q + 2) + r.val]'hidx).toNat =
      ref_ntt (q + 2)
        (((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ (q + 2)))⁻¹)
        (ntt_sub_input_inv n (q + 2) hq2 hm_eq v b) r := by
  simp only
  -- Make the prime fact explicit to avoid repeated instance search for ZMod field operations
  haveI hp : Fact (Nat.Prime mod32.toNat) := ⟨prime_3221225473⟩
  -- Setup basic parameters (mirrors radix4Middle_advances_inv)
  have hn64 : n < 64 := n_lt_64_of_pow2_nat m n hm_eq hm_dvd
  have hs_eq : (len >>> 1).toNat = 2 ^ q := by
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, hlen, Nat.pow_succ',
               (by decide : (1 : UInt64).toNat % 64 = 1), pow_one]; omega
  set s : UInt64 := len >>> 1 with hs_def
  have hlen_butterfly : len.toNat = 2 * s.toNat := by rw [hs_eq, hlen]; ring
  have hdvd : 2 * len.toNat ∣ m := by
    rw [hm_eq, hlen, (by ring : 2 * 2 ^ (q + 1) = 2 ^ (q + 2))]
    exact pow_dvd_pow 2 hq2
  have hN_le : m ≤ 2 ^ 64 :=
    le_of_lt (by rw [hm_eq]; exact Nat.pow_lt_pow_right (by norm_num) hn64)
  -- Decompose r.val = quad * 2^q + j2nat
  have hr_lt : r.val < 2 ^ (q + 2) := r.isLt
  have hr_pow_eq : 2 ^ (q + 2) = 4 * 2 ^ q := by ring
  set j2nat : ℕ := r.val % 2 ^ q with hj2nat_def
  set quad : ℕ := r.val / 2 ^ q with hquad_def
  have hj2_lt : j2nat < 2 ^ q := Nat.mod_lt _ (Nat.two_pow_pos q)
  have hquad_lt : quad < 4 := by
    have hrlt' : r.val < 4 * 2 ^ q := hr_pow_eq ▸ hr_lt
    exact Nat.div_lt_iff_lt_mul (Nat.two_pow_pos q) |>.mpr (by linarith)
  have hr_decomp : r.val = quad * 2 ^ q + j2nat := by
    have h := Nat.div_add_mod r.val (2 ^ q)
    rw [hquad_def, hj2nat_def]
    linarith [Nat.mul_comm (2 ^ q) (r.val / 2 ^ q)]
  have hn_sub_eq : n - (q + 2) = n - q - 2 := by omega
  have hb_pow : b < 2 ^ (n - q - 2) := hn_sub_eq ▸ hb
  have hb_i2_lt : b * 2 ^ (q + 2) < 2 ^ n := by
    have : b * 2 ^ (q + 2) < 2 ^ (n - q - 2) * 2 ^ (q + 2) := by
      nlinarith [Nat.two_pow_pos (q + 2), hb_pow]
    rw [show (2 : ℕ) ^ (n - q - 2) * 2 ^ (q + 2) = 2 ^ n from by
      rw [← pow_add]; congr 1; omega] at this
    exact this
  have hb_i2_lt_64 : b * 2 ^ (q + 2) < 2 ^ 64 :=
    lt_of_lt_of_le hb_i2_lt (Nat.pow_le_pow_right (by decide) (by omega))
  set i2 : UInt64 := (b * 2 * len.toNat).toUInt64 with hi2_def
  have hi2_toNat : i2.toNat = b * 2 ^ (q + 2) := by
    rw [hi2_def]
    have h1 : b * 2 * len.toNat = b * 2 ^ (q + 2) := by rw [hlen]; ring
    rw [show b * 2 * len.toNat = b * 2 ^ (q + 2) from h1]
    exact nat_toUInt64_faithful _ hb_i2_lt_64
  set j2u : UInt64 := j2nat.toUInt64 with hj2u_def
  have hj2u_toNat : j2u.toNat = j2nat := by
    rw [hj2u_def]
    apply nat_toUInt64_faithful
    exact lt_of_lt_of_le (lt_of_lt_of_le hj2_lt
      (Nat.pow_le_pow_right (by decide) (show q ≤ n by omega)))
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hj2_lt_s : j2u.toNat < s.toNat := by rw [hj2u_toNat, hs_eq]; exact hj2_lt
  -- Position arithmetic: specific (j2nat) and generic (∀ j2 < 2^q),
  -- both via ntt_block_pos_arith_nat
  obtain ⟨_, h_i2_j2_toNat, h_i2_j2_s_toNat, h_i2_len_j2_toNat, h_i2_len_j2_s_toNat,
      hbnd0, hbnd1, hbnd2, hbnd3⟩ :=
    ntt_block_pos_arith_nat n q hq2 hm_eq hn64 len hlen b j2nat hb_pow hj2_lt
  simp only [← hi2_def, ← hj2u_def, ← hs_def] at h_i2_j2_toNat h_i2_j2_s_toNat
  simp only [← hi2_def, ← hj2u_def, ← hs_def] at h_i2_len_j2_toNat h_i2_len_j2_s_toNat
  simp only [← hi2_def, ← hj2u_def, ← hs_def] at hbnd0 hbnd1 hbnd2 hbnd3
  have hbp1 : (b + 1) * 2 ^ (q + 2) ≤ 2 ^ n :=
    calc (b + 1) * 2 ^ (q + 2)
        ≤ 2 ^ (n - q - 2) * 2 ^ (q + 2) := Nat.mul_le_mul_right _ hb_pow
      _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
  -- Position-match relations
  have hpos0_match : (i2 + j2u).toNat = (4 * b + 0) * 2 ^ q + j2nat := by
    rw [h_i2_j2_toNat]; ring
  have hpos1_match : (i2 + j2u + s).toNat = (4 * b + 1) * 2 ^ q + j2nat := by
    rw [h_i2_j2_s_toNat]; ring
  have hpos2_match : (i2 + len + j2u).toNat = (4 * b + 2) * 2 ^ q + j2nat := by
    rw [h_i2_len_j2_toNat]; ring
  have hpos3_match : (i2 + len + j2u + s).toNat = (4 * b + 3) * 2 ^ q + j2nat := by
    rw [h_i2_len_j2_s_toNat]; ring
  have hb_idx_eq : (b * 2 ^ (q + 2) + r.val) = b * 2 ^ (q + 2) + quad * 2 ^ q + j2nat := by
    rw [hr_decomp]; ring
  -- Split radix4Inner into leading (j2nat steps), butterfly at j2u, and trailing
  have hs_split : s.toNat = j2nat + (1 + (s.toNat - j2nat - 1)) := by rw [hs_eq]; omega
  have h_split := radix4Inner_split_at true roots a s.toNat len.toNat i2.toNat j2nat hs_split
  -- Generic position formulas for any j2 < 2^q, via ntt_block_pos_arith_nat
  have h_pos0_gen : ∀ j2 : ℕ, j2 < 2 ^ q →
      (i2 + j2.toUInt64).toNat = b * 2 ^ (q + 2) + j2 :=
    fun j2 hj2 =>
      (ntt_block_pos_arith_nat n q hq2 hm_eq hn64 len hlen b j2 hb_pow hj2).2.1
  have h_pos1_gen : ∀ j2 : ℕ, j2 < 2 ^ q →
      (i2 + j2.toUInt64 + s).toNat = b * 2 ^ (q + 2) + j2 + 2 ^ q :=
    fun j2 hj2 =>
      (ntt_block_pos_arith_nat n q hq2 hm_eq hn64 len hlen b j2 hb_pow hj2).2.2.1
  have h_pos2_gen : ∀ j2 : ℕ, j2 < 2 ^ q →
      (i2 + len + j2.toUInt64).toNat = b * 2 ^ (q + 2) + j2 + 2 ^ (q + 1) :=
    fun j2 hj2 =>
      (ntt_block_pos_arith_nat n q hq2 hm_eq hn64 len hlen b j2 hb_pow hj2).2.2.2.1
  have h_pos3_gen : ∀ j2 : ℕ, j2 < 2 ^ q →
      (i2 + len + j2.toUInt64 + s).toNat =
        b * 2 ^ (q + 2) + j2 + 2 ^ (q + 1) + 2 ^ q :=
    fun j2 hj2 =>
      (ntt_block_pos_arith_nat n q hq2 hm_eq hn64 len hlen b j2 hb_pow hj2).2.2.2.2.1
  have h_bnd_gen : ∀ j2 : ℕ, j2 < 2 ^ q →
      (i2 + j2.toUInt64).toNat < m ∧ (i2 + j2.toUInt64 + s).toNat < m ∧
      (i2 + len + j2.toUInt64).toNat < m ∧
      (i2 + len + j2.toUInt64 + s).toNat < m := by
    intro j2 hj2
    obtain ⟨_, _, _, _, _, h5, h6, h7, h8⟩ :=
      ntt_block_pos_arith_nat n q hq2 hm_eq hn64 len hlen b j2 hb_pow hj2
    exact ⟨h5, h6, h7, h8⟩
  -- ℕ-form bounds: i2.toNat + j2 < m etc. (used by radix4Inner_getElem_ne_gen)
  have h_bnd_gen_nat : ∀ j2 : ℕ, j2 < 2 ^ q →
      i2.toNat + j2 < m ∧ i2.toNat + j2 + s.toNat < m ∧
      i2.toNat + len.toNat + j2 < m ∧
      i2.toNat + len.toNat + j2 + s.toNat < m := by
    intro j2 hj2
    have h := h_bnd_gen j2 hj2
    rw [h_pos0_gen j2 hj2, h_pos1_gen j2 hj2, h_pos2_gen j2 hj2, h_pos3_gen j2 hj2] at h
    simp only [hi2_toNat, hs_eq, hlen] at *
    exact ⟨h.1, h.2.1, by omega, by omega⟩
  have h_ne_gen : ∀ j2 : ℕ, j2 < 2 ^ q → j2 ≠ j2nat →
      ∀ posval, posval = b * 2 ^ (q + 2) + j2nat ∨
                posval = b * 2 ^ (q + 2) + j2nat + 2 ^ q ∨
                posval = b * 2 ^ (q + 2) + j2nat + 2 ^ (q + 1) ∨
                posval = b * 2 ^ (q + 2) + j2nat + 2 ^ (q + 1) + 2 ^ q →
      (i2 + j2.toUInt64).toNat ≠ posval ∧ (i2 + j2.toUInt64 + s).toNat ≠ posval ∧
      (i2 + len + j2.toUInt64).toNat ≠ posval ∧
      (i2 + len + j2.toUInt64 + s).toNat ≠ posval :=
    fun j2 hj2 hj2_ne posval hpos =>
      let res := radix4_block_ne_pos q b j2 j2nat hj2 hj2_lt hj2_ne posval hpos
      ⟨h_pos0_gen j2 hj2 ▸ res.1,
       h_pos1_gen j2 hj2 ▸ res.2.1,
       h_pos2_gen j2 hj2 ▸ res.2.2.1,
       h_pos3_gen j2 hj2 ▸ res.2.2.2⟩
  -- Combinator: radix4Inner with any range doesn't modify butterfly positions
  have h_ne_at : ∀ (B : Vector UInt32 m) (nsteps start posval : ℕ) (hbnd : posval < m),
      (posval = b * 2 ^ (q + 2) + j2nat ∨ posval = b * 2 ^ (q + 2) + j2nat + 2 ^ q ∨
       posval = b * 2 ^ (q + 2) + j2nat + 2 ^ (q + 1) ∨
       posval = b * 2 ^ (q + 2) + j2nat + 2 ^ (q + 1) + 2 ^ q) →
      (∀ j2, start ≤ j2 → j2 < start + nsteps → j2 < 2 ^ q) →
      (∀ j2, start ≤ j2 → j2 < start + nsteps → j2 ≠ j2nat) →
      (radix4Inner true roots s.toNat len.toNat i2.toNat nsteps start B)[posval]'hbnd =
        B[posval]'hbnd := by
    intro B nsteps start posval hbnd hpos hlt_range hne
    apply radix4Inner_getElem_ne_gen true roots B
      s.toNat len.toNat i2.toNat nsteps start posval hbnd
    · intro j2 hlo hhi; exact h_bnd_gen_nat j2 (hlt_range j2 hlo hhi)
    · intro j2 hlo hhi
      have hj2lt := hlt_range j2 hlo hhi
      obtain ⟨hn0, hn1, hn2, hn3⟩ := h_ne_gen j2 hj2lt (hne j2 hlo hhi) posval hpos
      rw [h_pos0_gen j2 hj2lt] at hn0
      rw [h_pos1_gen j2 hj2lt] at hn1
      rw [h_pos2_gen j2 hj2lt] at hn2
      rw [h_pos3_gen j2 hj2lt] at hn3
      simp only [hi2_toNat, hs_eq, hlen]
      exact ⟨hn0, hn1, by omega, by omega⟩
  have h_leading_pos0 := h_ne_at a j2nat 0 _ hbnd0 (Or.inl h_i2_j2_toNat)
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).trans hj2_lt)
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).ne)
  have h_leading_pos1 := h_ne_at a j2nat 0 _ hbnd1 (Or.inr (Or.inl h_i2_j2_s_toNat))
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).trans hj2_lt)
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).ne)
  have h_leading_pos2 := h_ne_at a j2nat 0 _ hbnd2
      (Or.inr (Or.inr (Or.inl h_i2_len_j2_toNat)))
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).trans hj2_lt)
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).ne)
  have h_leading_pos3 := h_ne_at a j2nat 0 _ hbnd3
      (Or.inr (Or.inr (Or.inr h_i2_len_j2_s_toNat)))
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).trans hj2_lt)
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).ne)
  have h_trail_bound : j2nat + 1 + (s.toNat - j2nat - 1) ≤ 2 ^ q :=
    hs_eq ▸ (add_assoc j2nat 1 _).symm ▸ hs_split ▸ le_refl s.toNat
  have h_trailing_pos0 : ∀ B,
      (radix4Inner true roots s.toNat len.toNat i2.toNat
        (s.toNat - j2nat - 1) (j2nat + 1) B)[(i2 + j2u).toNat]'hbnd0 =
      B[(i2 + j2u).toNat]'hbnd0 :=
    fun B => h_ne_at B _ _ _ hbnd0 (Or.inl h_i2_j2_toNat)
      (fun _ _ hhi => Nat.lt_of_lt_of_le hhi h_trail_bound)
      (fun _ hlo _ => Nat.ne_of_gt (Nat.lt_of_succ_le hlo))
  have h_trailing_pos1 : ∀ B,
      (radix4Inner true roots s.toNat len.toNat i2.toNat
        (s.toNat - j2nat - 1) (j2nat + 1) B)[(i2 + j2u + s).toNat]'hbnd1 =
      B[(i2 + j2u + s).toNat]'hbnd1 :=
    fun B => h_ne_at B _ _ _ hbnd1 (Or.inr (Or.inl h_i2_j2_s_toNat))
      (fun _ _ hhi => Nat.lt_of_lt_of_le hhi h_trail_bound)
      (fun _ hlo _ => Nat.ne_of_gt (Nat.lt_of_succ_le hlo))
  have h_trailing_pos2 : ∀ B,
      (radix4Inner true roots s.toNat len.toNat i2.toNat
        (s.toNat - j2nat - 1) (j2nat + 1) B)[(i2 + len + j2u).toNat]'hbnd2 =
      B[(i2 + len + j2u).toNat]'hbnd2 :=
    fun B => h_ne_at B _ _ _ hbnd2 (Or.inr (Or.inr (Or.inl h_i2_len_j2_toNat)))
      (fun _ _ hhi => Nat.lt_of_lt_of_le hhi h_trail_bound)
      (fun _ hlo _ => Nat.ne_of_gt (Nat.lt_of_succ_le hlo))
  have h_trailing_pos3 : ∀ B,
      (radix4Inner true roots s.toNat len.toNat i2.toNat
        (s.toNat - j2nat - 1) (j2nat + 1) B)[(i2 + len + j2u + s).toNat]'hbnd3 =
      B[(i2 + len + j2u + s).toNat]'hbnd3 :=
    fun B => h_ne_at B _ _ _ hbnd3 (Or.inr (Or.inr (Or.inr h_i2_len_j2_s_toNat)))
      (fun _ _ hhi => Nat.lt_of_lt_of_le hhi h_trail_bound)
      (fun _ hlo _ => Nat.ne_of_gt (Nat.lt_of_succ_le hlo))
  -- Apply butterfly4_inverse_ZMod_combined to the leading vector.
  set A_lead := radix4Inner true roots s.toNat len.toNat i2.toNat j2nat 0 a with hA_lead_def
  have hA_lead_bnd : A_lead.all (· < mod32) := by
    rw [hA_lead_def]
    exact radix4Inner_bound true roots s.toNat len.toNat i2.toNat j2nat 0 a ha_bnd
  have hN_dvd_m : m ∣ mod64.toNat - 1 := hm_dvd
  -- ℕ-form bounds for butterfly4_inverse_ZMod_combined (derived from h_bnd_gen_nat j2nat)
  have hbnd0_nat : i2.toNat + j2u.toNat < m :=
    hj2u_toNat ▸ (h_bnd_gen_nat j2nat hj2_lt).1
  have hbnd1_nat : i2.toNat + j2u.toNat + s.toNat < m :=
    hj2u_toNat ▸ (h_bnd_gen_nat j2nat hj2_lt).2.1
  have hbnd2_nat : i2.toNat + len.toNat + j2u.toNat < m :=
    hj2u_toNat ▸ (h_bnd_gen_nat j2nat hj2_lt).2.2.1
  have hbnd3_nat : i2.toNat + len.toNat + j2u.toNat + s.toNat < m :=
    hj2u_toNat ▸ (h_bnd_gen_nat j2nat hj2_lt).2.2.2
  have hbf := butterfly4_inverse_ZMod_combined roots A_lead hA_lead_bnd hroots hroots_bnd
    s.toNat len.toNat i2.toNat j2u.toNat hlen_butterfly hdvd hN_dvd_m hj2_lt_s
    hbnd0_nat hbnd1_nat hbnd2_nat hbnd3_nat
  obtain ⟨hbf0, hbf2, hbf1, hbf3⟩ := hbf
  -- Substitute h_leading_posK in the A_k expressions: A_lead[posK] = a[posK]
  -- Compute A_k values via h_inv_k
  -- Setup ωq and ω_top abbreviations
  set ωq : ZMod mod32.toNat :=
    ((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ q))⁻¹ with hωq_def
  set ω_top : ZMod mod32.toNat :=
    ((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ (q + 2)))⁻¹ with hω_top_def
  -- ω_top^4 = ωq because 2^(q+2) ∣ mod64-1
  have h_dvd_q2 : 2 ^ (q + 2) ∣ mod64.toNat - 1 :=
    dvd_trans (pow_dvd_pow 2 hq2) h_dvd
  have h_dvd_q1 : 2 ^ (q + 1) ∣ mod64.toNat - 1 :=
    dvd_trans (pow_dvd_pow 2 (by omega : q + 1 ≤ q + 2)) h_dvd_q2
  have h2len_eq : 2 * len.toNat = 2 ^ (q + 2) := by rw [hlen]; ring
  -- ω_top^4 = ωq  (both inverses; (a⁻¹)^4 = (a^4)⁻¹)
  have h_omega_q : ω_top ^ 4 = ωq := by
    rw [hωq_def, hω_top_def, inv_pow, ← pow_mul]
    congr 2
    obtain ⟨K, hK⟩ := h_dvd_q2
    have hpos : (2 : ℕ) ^ (q + 2) > 0 := Nat.two_pow_pos _
    have hpos_q : (2 : ℕ) ^ q > 0 := Nat.two_pow_pos _
    rw [hK, Nat.mul_div_cancel_left _ hpos, (by ring : (2 : ℕ) ^ (q + 2) = 4 * 2 ^ q),
        (by ring : 4 * 2 ^ q * K = 2 ^ q * (4 * K)), Nat.mul_div_cancel_left _ hpos_q]
    ring
  -- Express the inverse twiddles τ₁, τ₂, τ₃ in terms of ω_top
  obtain ⟨h_tau1_base, h_tau2_base, h_tau3_base⟩ :=
    inv_twiddle_eqs q j2nat hj2_lt h_dvd_q1 h_dvd_q2 ω_top hω_top_def
  have h_tau2 : (primRoot.toNat : ZMod mod32.toNat) ^
      ((mod64.toNat - 1) / (2 * len.toNat) * (2 * len.toNat - j2u.toNat)) = ω_top ^ j2nat := by
    rw [h2len_eq, hj2u_toNat]; exact h_tau2_base
  have h_tau3 : (primRoot.toNat : ZMod mod32.toNat) ^
      ((mod64.toNat - 1) / (2 * len.toNat) * (2 * len.toNat - s.toNat - j2u.toNat)) =
        ω_top ^ (2 ^ q + j2nat) := by
    rw [h2len_eq, hs_eq, hj2u_toNat]; exact h_tau3_base
  have h_tau1 : (primRoot.toNat : ZMod mod32.toNat) ^
      ((mod64.toNat - 1) / len.toNat * (len.toNat - j2u.toNat)) = (ω_top ^ 2) ^ j2nat := by
    rw [hlen, hj2u_toNat]; exact h_tau1_base
  -- Compute A₀ via h_inv_k and ntt_sub_input_inv_block_0
  have hb_pow' : b < 2 ^ (n - q - 2) := hb_pow
  have h_idx_in_bnd : ∀ k, k < 4 → (4 * b + k) * 2 ^ q + j2nat < m :=
    fun k hk => hm_eq ▸ block_idx_lt q b k j2nat n hk hb_pow hj2_lt hq2
  -- A-values from h_inv_k
  have hA0_eq : ((A_lead[(i2 + j2u).toNat]'hbnd0).toNat : ZMod mod32.toNat) =
      ref_ntt q ωq (ntt_sub_input_inv n q (by omega) hm_eq v (4 * b + 0)) ⟨j2nat, hj2_lt⟩ := by
    rw [h_leading_pos0]
    have h := h_inv_k 0 (by decide) ⟨j2nat, hj2_lt⟩ (h_idx_in_bnd 0 (by decide))
    have heq : a[(i2 + j2u).toNat]'hbnd0 =
        a[(4 * b + 0) * 2 ^ q + j2nat]'(h_idx_in_bnd 0 (by decide)) :=
      getElem_congr_idx hpos0_match
    rw [heq]; exact h
  have hA1_eq : ((A_lead[(i2 + j2u + s).toNat]'hbnd1).toNat : ZMod mod32.toNat) =
      ref_ntt q ωq (ntt_sub_input_inv n q (by omega) hm_eq v (4 * b + 1)) ⟨j2nat, hj2_lt⟩ := by
    rw [h_leading_pos1]
    have h := h_inv_k 1 (by decide) ⟨j2nat, hj2_lt⟩ (h_idx_in_bnd 1 (by decide))
    have heq : a[(i2 + j2u + s).toNat]'hbnd1 =
        a[(4 * b + 1) * 2 ^ q + j2nat]'(h_idx_in_bnd 1 (by decide)) :=
      getElem_congr_idx hpos1_match
    rw [heq]; exact h
  have hA2_eq : ((A_lead[(i2 + len + j2u).toNat]'hbnd2).toNat : ZMod mod32.toNat) =
      ref_ntt q ωq (ntt_sub_input_inv n q (by omega) hm_eq v (4 * b + 2)) ⟨j2nat, hj2_lt⟩ := by
    rw [h_leading_pos2]
    have h := h_inv_k 2 (by decide) ⟨j2nat, hj2_lt⟩ (h_idx_in_bnd 2 (by decide))
    have heq : a[(i2 + len + j2u).toNat]'hbnd2 =
        a[(4 * b + 2) * 2 ^ q + j2nat]'(h_idx_in_bnd 2 (by decide)) :=
      getElem_congr_idx hpos2_match
    rw [heq]; exact h
  have hA3_eq : ((A_lead[(i2 + len + j2u + s).toNat]'hbnd3).toNat : ZMod mod32.toNat) =
      ref_ntt q ωq (ntt_sub_input_inv n q (by omega) hm_eq v (4 * b + 3)) ⟨j2nat, hj2_lt⟩ := by
    rw [h_leading_pos3]
    have h := h_inv_k 3 (by decide) ⟨j2nat, hj2_lt⟩ (h_idx_in_bnd 3 (by decide))
    have heq : a[(i2 + len + j2u + s).toNat]'hbnd3 =
        a[(4 * b + 3) * 2 ^ q + j2nat]'(h_idx_in_bnd 3 (by decide)) :=
      getElem_congr_idx hpos3_match
    rw [heq]; exact h
  -- Use ntt_sub_input_block_K to rewrite the ntt_sub_input expressions in terms of v at b
  -- Define the f function for ref_ntt at level q+2:
  set f_ntt : Fin (2 ^ (q + 2)) → ZMod mod32.toNat :=
    ntt_sub_input_inv n (q + 2) hq2 hm_eq v b with hf_ntt_def
  have h_sub0_fun : ntt_sub_input_inv n q (by omega) hm_eq v (4 * b + 0) =
      fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val, fin_4mul_lt q j⟩ := by
    funext j
    rw [hf_ntt_def]
    simpa using ntt_sub_input_inv_block_0 n q hq2 hm_eq v b hb_pow' j
  have h_sub1_fun : ntt_sub_input_inv n q (by omega) hm_eq v (4 * b + 1) =
      fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 2, fin_4mul2_lt q j⟩ := by
    funext j
    rw [hf_ntt_def]
    simpa using ntt_sub_input_inv_block_1 n q hq2 hm_eq v b j
  have h_sub2_fun : ntt_sub_input_inv n q (by omega) hm_eq v (4 * b + 2) =
      fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 1, fin_4mul1_lt q j⟩ := by
    funext j
    rw [hf_ntt_def]
    simpa using ntt_sub_input_inv_block_2 n q hq2 hm_eq v b j
  have h_sub3_fun : ntt_sub_input_inv n q (by omega) hm_eq v (4 * b + 3) =
      fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 3, fin_4mul3_lt q j⟩ := by
    funext j
    rw [hf_ntt_def]
    simpa using ntt_sub_input_inv_block_3 n q hq2 hm_eq v b hb_pow' j
  -- Index-equality bridge lemmas: UInt64-toNat ↔ ℕ-addition
  have h_add0 : (i2 + j2u).toNat = i2.toNat + j2u.toNat := by
    rw [h_i2_j2_toNat, hi2_toNat, hj2u_toNat]
  have h_add1 : (i2 + j2u + s).toNat = i2.toNat + j2u.toNat + s.toNat := by
    rw [h_i2_j2_s_toNat, hi2_toNat, hj2u_toNat, hs_eq]
  have h_add2 : (i2 + len + j2u).toNat = i2.toNat + len.toNat + j2u.toNat := by
    rw [h_i2_len_j2_toNat, hi2_toNat, hj2u_toNat, hlen]; ring
  have h_add3 : (i2 + len + j2u + s).toNat = i2.toNat + len.toNat + j2u.toNat + s.toNat := by
    rw [h_i2_len_j2_s_toNat, hi2_toNat, hj2u_toNat, hlen, hs_eq]; ring
  -- Restate A-value equalities with ℕ-add indices to match butterfly4_inverse output
  have hA0_final : ((A_lead[i2.toNat + j2u.toNat]'hbnd0_nat).toNat : ZMod mod32.toNat) =
      ref_ntt q (ω_top ^ 4)
        (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val, fin_4mul_lt q j⟩) ⟨j2nat, hj2_lt⟩ := by
    rw [show A_lead[i2.toNat + j2u.toNat]'hbnd0_nat = A_lead[(i2 + j2u).toNat]'hbnd0 from
          getElem_congr_idx h_add0.symm, hA0_eq, h_omega_q, ← h_sub0_fun]
  have hA1_final : ((A_lead[i2.toNat + j2u.toNat + s.toNat]'hbnd1_nat).toNat : ZMod mod32.toNat) =
      ref_ntt q (ω_top ^ 4)
        (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 2, fin_4mul2_lt q j⟩)
        ⟨j2nat, hj2_lt⟩ := by
    rw [show A_lead[i2.toNat + j2u.toNat + s.toNat]'hbnd1_nat =
          A_lead[(i2 + j2u + s).toNat]'hbnd1 from
          getElem_congr_idx h_add1.symm, hA1_eq, h_omega_q, ← h_sub1_fun]
  have hA2_final : ((A_lead[i2.toNat + len.toNat + j2u.toNat]'hbnd2_nat).toNat :
      ZMod mod32.toNat) =
      ref_ntt q (ω_top ^ 4)
        (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 1, fin_4mul1_lt q j⟩)
        ⟨j2nat, hj2_lt⟩ := by
    rw [show A_lead[i2.toNat + len.toNat + j2u.toNat]'hbnd2_nat =
          A_lead[(i2 + len + j2u).toNat]'hbnd2 from
          getElem_congr_idx h_add2.symm, hA2_eq, h_omega_q, ← h_sub2_fun]
  have hA3_final : ((A_lead[i2.toNat + len.toNat + j2u.toNat + s.toNat]'hbnd3_nat).toNat :
      ZMod mod32.toNat) =
      ref_ntt q (ω_top ^ 4)
        (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 3, fin_4mul3_lt q j⟩)
        ⟨j2nat, hj2_lt⟩ := by
    rw [show A_lead[i2.toNat + len.toNat + j2u.toNat + s.toNat]'hbnd3_nat =
          A_lead[(i2 + len + j2u + s).toNat]'hbnd3 from
          getElem_congr_idx h_add3.symm, hA3_eq, h_omega_q, ← h_sub3_fun]
  -- Now case-split on quad via the isolated helper (interval_cases runs in minimal context)
  simp only [hA0_final, hA1_final, hA2_final, hA3_final] at hbf0 hbf1 hbf2 hbf3
  exact radix4InnerInv_case_split q b r j2nat quad hp hj2_lt hquad_lt hr_decomp hidx
    i2 j2u s len ω_top f_ntt A_lead roots a
    hbnd0 hbnd1 hbnd2 hbnd3 hbnd0_nat hbnd1_nat hbnd2_nat hbnd3_nat
    h_i2_j2_toNat h_i2_j2_s_toNat h_i2_len_j2_toNat h_i2_len_j2_s_toNat
    hj2u_toNat h_add0 h_add1 h_add2 h_add3
    h_split h_trailing_pos0 h_trailing_pos1 h_trailing_pos2 h_trailing_pos3
    hbf0 hbf1 hbf2 hbf3 h_tau1 h_tau2 h_tau3
