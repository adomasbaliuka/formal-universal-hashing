/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import UniversalHashing.BinConvolution.ConvolutionHelpers.DFTLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.MontgomeryLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.RootTableLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.NttBoundLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.Radix4ForwardLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpers



/-!
# Single-block radix-4 correctness

This file contains `radix4Inner_single_block_correct`, split out from `OuterLoopHelpers`
to keep per-file elaboration memory bounded.
-/

/-- Proves that a butterfly at j2 ≠ j2nat does not touch any of the four
    block positions corresponding to j2nat. Isolated here so omega runs with
    minimal context (avoids slow hypothesis scanning in the 16-call rcases). -/
private lemma nat_trail_bound (j k : ℕ) (h : j < k) : j + 1 + (k - j - 1) ≤ k := by omega

private lemma radix4Inner_case_split {m : ℕ} (q b : ℕ) (r : Fin (2 ^ (q + 2)))
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
    (h_i2_j2_toNat : (i2 + j2u).toNat = b * 2 ^ (q + 2) + j2nat)
    (h_i2_j2_s_toNat : (i2 + j2u + s).toNat = b * 2 ^ (q + 2) + j2nat + 2 ^ q)
    (h_i2_len_j2_toNat : (i2 + len + j2u).toNat = b * 2 ^ (q + 2) + j2nat + 2 ^ (q + 1))
    (h_i2_len_j2_s_toNat :
        (i2 + len + j2u + s).toNat = b * 2 ^ (q + 2) + j2nat + 2 ^ (q + 1) + 2 ^ q)
    (h_split :
        radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat 0 a =
        radix4Inner false roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1) (j2nat + 1)
          (butterfly4 A_lead false roots s.toNat len.toNat i2.toNat j2u.toNat))
    (h_trailing_pos0 : ∀ B : Vector UInt32 m,
        (radix4Inner false roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
            (j2nat + 1) B)[(i2 + j2u).toNat]'hbnd0 = B[(i2 + j2u).toNat]'hbnd0)
    (h_trailing_pos1 : ∀ B : Vector UInt32 m,
        (radix4Inner false roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
            (j2nat + 1) B)[(i2 + j2u + s).toNat]'hbnd1 = B[(i2 + j2u + s).toNat]'hbnd1)
    (h_trailing_pos2 : ∀ B : Vector UInt32 m,
        (radix4Inner false roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
            (j2nat + 1) B)[(i2 + len + j2u).toNat]'hbnd2 = B[(i2 + len + j2u).toNat]'hbnd2)
    (h_trailing_pos3 : ∀ B : Vector UInt32 m,
        (radix4Inner false roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
            (j2nat + 1) B)[(i2 + len + j2u + s).toNat]'hbnd3 =
            B[(i2 + len + j2u + s).toNat]'hbnd3)
    (hbf0 : (((butterfly4 A_lead false roots s.toNat len.toNat i2.toNat
                  j2u.toNat)[(i2 + j2u).toNat]'hbnd0).toNat : ZMod mod32.toNat) =
        ref_ntt q (ω_top ^ 4)
            (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val, fin_4mul_lt q j⟩)
            ⟨j2nat, hj2_lt⟩ +
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / len.toNat * j2u.toNat) *
            ref_ntt q (ω_top ^ 4)
              (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 2, fin_4mul2_lt q j⟩)
              ⟨j2nat, hj2_lt⟩ +
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / (2 * len.toNat) * j2u.toNat) *
            (ref_ntt q (ω_top ^ 4)
                (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 1, fin_4mul1_lt q j⟩)
                ⟨j2nat, hj2_lt⟩ +
              (primRoot.toNat : ZMod mod32.toNat) ^
                  ((mod64.toNat - 1) / len.toNat * j2u.toNat) *
                ref_ntt q (ω_top ^ 4)
                  (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 3, fin_4mul3_lt q j⟩)
                  ⟨j2nat, hj2_lt⟩))
    (hbf1 : (((butterfly4 A_lead false roots s.toNat len.toNat i2.toNat
                  j2u.toNat)[(i2 + j2u + s).toNat]'hbnd1).toNat : ZMod mod32.toNat) =
        ref_ntt q (ω_top ^ 4)
            (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val, fin_4mul_lt q j⟩)
            ⟨j2nat, hj2_lt⟩ -
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / len.toNat * j2u.toNat) *
            ref_ntt q (ω_top ^ 4)
              (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 2, fin_4mul2_lt q j⟩)
              ⟨j2nat, hj2_lt⟩ +
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / (2 * len.toNat) * (s.toNat + j2u.toNat)) *
            (ref_ntt q (ω_top ^ 4)
                (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 1, fin_4mul1_lt q j⟩)
                ⟨j2nat, hj2_lt⟩ -
              (primRoot.toNat : ZMod mod32.toNat) ^
                  ((mod64.toNat - 1) / len.toNat * j2u.toNat) *
                ref_ntt q (ω_top ^ 4)
                  (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 3, fin_4mul3_lt q j⟩)
                  ⟨j2nat, hj2_lt⟩))
    (hbf2 : (((butterfly4 A_lead false roots s.toNat len.toNat i2.toNat
                  j2u.toNat)[(i2 + len + j2u).toNat]'hbnd2).toNat : ZMod mod32.toNat) =
        ref_ntt q (ω_top ^ 4)
            (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val, fin_4mul_lt q j⟩)
            ⟨j2nat, hj2_lt⟩ +
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / len.toNat * j2u.toNat) *
            ref_ntt q (ω_top ^ 4)
              (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 2, fin_4mul2_lt q j⟩)
              ⟨j2nat, hj2_lt⟩ -
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / (2 * len.toNat) * j2u.toNat) *
            (ref_ntt q (ω_top ^ 4)
                (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 1, fin_4mul1_lt q j⟩)
                ⟨j2nat, hj2_lt⟩ +
              (primRoot.toNat : ZMod mod32.toNat) ^
                  ((mod64.toNat - 1) / len.toNat * j2u.toNat) *
                ref_ntt q (ω_top ^ 4)
                  (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 3, fin_4mul3_lt q j⟩)
                  ⟨j2nat, hj2_lt⟩))
    (hbf3 : (((butterfly4 A_lead false roots s.toNat len.toNat i2.toNat
                  j2u.toNat)[(i2 + len + j2u + s).toNat]'hbnd3).toNat : ZMod mod32.toNat) =
        ref_ntt q (ω_top ^ 4)
            (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val, fin_4mul_lt q j⟩)
            ⟨j2nat, hj2_lt⟩ -
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / len.toNat * j2u.toNat) *
            ref_ntt q (ω_top ^ 4)
              (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 2, fin_4mul2_lt q j⟩)
              ⟨j2nat, hj2_lt⟩ -
          (primRoot.toNat : ZMod mod32.toNat) ^
              ((mod64.toNat - 1) / (2 * len.toNat) * (s.toNat + j2u.toNat)) *
            (ref_ntt q (ω_top ^ 4)
                (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 1, fin_4mul1_lt q j⟩)
                ⟨j2nat, hj2_lt⟩ -
              (primRoot.toNat : ZMod mod32.toNat) ^
                  ((mod64.toNat - 1) / len.toNat * j2u.toNat) *
                ref_ntt q (ω_top ^ 4)
                  (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 3, fin_4mul3_lt q j⟩)
                  ⟨j2nat, hj2_lt⟩))
    (h_tau1 : (primRoot.toNat : ZMod mod32.toNat) ^
        ((mod64.toNat - 1) / len.toNat * j2u.toNat) = (ω_top ^ 2) ^ j2nat)
    (h_tau2 : (primRoot.toNat : ZMod mod32.toNat) ^
        ((mod64.toNat - 1) / (2 * len.toNat) * j2u.toNat) = ω_top ^ j2nat)
    (h_tau3 : (primRoot.toNat : ZMod mod32.toNat) ^
        ((mod64.toNat - 1) / (2 * len.toNat) * (s.toNat + j2u.toNat)) =
        ω_top ^ (2 ^ q + j2nat)) :
    ((radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat
          0 a)[b * 2 ^ (q + 2) + r.val]'hidx).toNat =
      ref_ntt (q + 2) ω_top f_ntt r := by
  haveI := hp
  interval_cases quad
  · -- quad = 0: idx-position is (i2 + j2u).toNat = b*2^(q+2) + j2nat
    have hidx_eq : b * 2 ^ (q + 2) + r.val = (i2 + j2u).toNat := by
      rw [h_i2_j2_toNat, hr_decomp]; ring
    have hsplit_idx :
        (radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat
            0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
        (butterfly4 A_lead false roots s.toNat len.toNat i2.toNat
            j2u.toNat)[(i2 + j2u).toNat]'hbnd0 := by
      have h1 :
          (radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
          (radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[(i2 + j2u).toNat]'hbnd0 :=
        getElem_congr_idx hidx_eq
      rw [h1, h_split, h_trailing_pos0]
    rw [hsplit_idx, hbf0, h_tau1, h_tau2]
    have hr_eq : r = ⟨j2nat, pow2q_lt_q2 q j2nat hj2_lt⟩ :=
      Fin.ext (hr_decomp.trans (by ring))
    rw [hr_eq, ref_ntt_radix4_q0]
  · -- quad = 1: idx-position is (i2 + j2u + s).toNat
    have hidx_eq : b * 2 ^ (q + 2) + r.val = (i2 + j2u + s).toNat := by
      rw [h_i2_j2_s_toNat, hr_decomp]; ring
    have hsplit_idx :
        (radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat
            0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
        (butterfly4 A_lead false roots s.toNat len.toNat i2.toNat
            j2u.toNat)[(i2 + j2u + s).toNat]'hbnd1 := by
      have h1 :
          (radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
          (radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[(i2 + j2u + s).toNat]'hbnd1 :=
        getElem_congr_idx hidx_eq
      rw [h1, h_split, h_trailing_pos1]
    rw [hsplit_idx, hbf1, h_tau1, h_tau3]
    have hr_eq : r = ⟨j2nat + 2 ^ q, pow2q_add_q_lt_q2 q j2nat hj2_lt⟩ :=
      Fin.ext (hr_decomp.trans (by ring))
    rw [hr_eq, ref_ntt_radix4_q1 q ω_top _ j2nat hj2_lt,
        show (2 : ℕ) ^ q + j2nat = j2nat + 2 ^ q from Nat.add_comm _ _]
  · -- quad = 2: idx-position is (i2 + len + j2u).toNat
    have hidx_eq : b * 2 ^ (q + 2) + r.val = (i2 + len + j2u).toNat := by
      rw [h_i2_len_j2_toNat, hr_decomp]; ring
    have hsplit_idx :
        (radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat
            0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
        (butterfly4 A_lead false roots s.toNat len.toNat i2.toNat
            j2u.toNat)[(i2 + len + j2u).toNat]'hbnd2 := by
      have h1 :
          (radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
          (radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[(i2 + len + j2u).toNat]'hbnd2 :=
        getElem_congr_idx hidx_eq
      rw [h1, h_split, h_trailing_pos2]
    rw [hsplit_idx, hbf2, h_tau1, h_tau2]
    have hr_eq : r = ⟨j2nat + 2 ^ (q + 1), pow2q_add_q1_lt_q2 q j2nat hj2_lt⟩ :=
      Fin.ext (hr_decomp.trans (by ring))
    rw [hr_eq, ref_ntt_radix4_q2]
  · -- quad = 3: idx-position is (i2 + len + j2u + s).toNat
    have hidx_eq : b * 2 ^ (q + 2) + r.val = (i2 + len + j2u + s).toNat := by
      rw [h_i2_len_j2_s_toNat, hr_decomp]; ring
    have hsplit_idx :
        (radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat
            0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
        (butterfly4 A_lead false roots s.toNat len.toNat i2.toNat
            j2u.toNat)[(i2 + len + j2u + s).toNat]'hbnd3 := by
      have h1 :
          (radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[b * 2 ^ (q + 2) + r.val]'hidx =
          (radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat
              0 a)[(i2 + len + j2u + s).toNat]'hbnd3 :=
        getElem_congr_idx hidx_eq
      rw [h1, h_split, h_trailing_pos3]
    rw [hsplit_idx, hbf3, h_tau1, h_tau3]
    have hr_eq : r = ⟨j2nat + 2 ^ q + 2 ^ (q + 1), pow2q_add_q_q1_lt_q2 q j2nat hj2_lt⟩ :=
      Fin.ext (hr_decomp.trans (by ring))
    rw [hr_eq, ref_ntt_radix4_q3 q ω_top _ j2nat hj2_lt,
        show (2 : ℕ) ^ q + j2nat = j2nat + 2 ^ q from Nat.add_comm _ _]

/-- The single-block step: applying radix4Inner for one block produces the correct
    ref_ntt(q+2) values at all positions in that block, reading inputs from the level-q invariant
    at the four input positions. -/
lemma radix4Inner_single_block_correct {m : ℕ} (n q : ℕ) (hq2 : q + 2 ≤ n)
    (hm_eq : m = 2 ^ n)
    (hm_dvd : m ∣ mod64.toNat - 1)
    (v : Vector UInt32 m)
    (roots : Vector UInt32 m)
    (hroots : ntt_roots_correct m roots)
    (hroots_bnd : roots.all (· < mod32))
    (h_dvd : 2 ^ n ∣ mod64.toNat - 1)
    (a : Vector UInt32 m)
    (ha_bnd : a.all (· < mod32))
    (len : UInt64) (hlen : len.toNat = 2 ^ (q + 1))
    (b : ℕ) (hb : b < 2 ^ (n - (q + 2)))
    (h_inv_k : ∀ k, k < 4 → ∀ (j2 : Fin (2 ^ q))
        (hidx_k : (4 * b + k) * 2 ^ q + j2.val < m),
        ((a[(4 * b + k) * 2 ^ q + j2.val]'hidx_k).toNat : ZMod mod32.toNat) =
          ref_ntt q
            ((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ q))
            (ntt_sub_input n q (by omega) hm_eq v (4 * b + k)) j2)
    (r : Fin (2 ^ (q + 2)))
    (hidx : b * 2 ^ (q + 2) + r.val < m) :
    let s := len >>> 1
    let i2 := (b * 2 * len.toNat).toUInt64
    ((radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat
        0 a)[b * 2 ^ (q + 2) + r.val]'hidx).toNat =
      ref_ntt (q + 2)
        ((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ (q + 2)))
        (ntt_sub_input n (q + 2) hq2 hm_eq v b) r := by
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
  -- Position arithmetic: specific (j2nat) via ntt_block_pos_arith_nat
  obtain ⟨_, h_i2_j2_toNat, h_i2_j2_s_toNat, h_i2_len_j2_toNat, h_i2_len_j2_s_toNat,
      hbnd0, hbnd1, hbnd2, hbnd3⟩ :=
    ntt_block_pos_arith_nat n q hq2 hm_eq hn64 len hlen b j2nat hb_pow hj2_lt
  simp only [← hi2_def, ← hj2u_def, ← hs_def] at h_i2_j2_toNat h_i2_j2_s_toNat
  simp only [← hi2_def, ← hj2u_def, ← hs_def] at h_i2_len_j2_toNat h_i2_len_j2_s_toNat
  simp only [← hi2_def, ← hj2u_def, ← hs_def] at hbnd0 hbnd1 hbnd2 hbnd3
  have hbp1 : (b + 1) * 2 ^ (q + 2) ≤ 2 ^ n :=
    calc (b + 1) * 2 ^ (q + 2) ≤ 2 ^ (n - q - 2) * 2 ^ (q + 2) := Nat.mul_le_mul_right _ hb_pow
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
  -- The 4 alternative position names in standard form
  have hb_idx_eq : (b * 2 ^ (q + 2) + r.val) = b * 2 ^ (q + 2) + quad * 2 ^ q + j2nat := by
    rw [hr_decomp]; ring
  -- Split radix4Inner into leading (j2nat steps), butterfly at j2u, and trailing
  -- s.toNat = j2nat + (1 + (s.toNat - j2nat - 1))
  have hs_split : s.toNat = j2nat + (1 + (s.toNat - j2nat - 1)) := by
    rw [hs_eq]; omega
  have h_split :
      radix4Inner false roots s.toNat len.toNat i2.toNat s.toNat 0 a =
      radix4Inner false roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1) (j2nat + 1)
        (butterfly4 (radix4Inner false roots s.toNat len.toNat i2.toNat j2nat 0 a)
            false roots s.toNat len.toNat i2.toNat j2u.toNat) := by
    conv_lhs => rw [hs_split, radix4Inner_comp]
    -- First split: radix4Inner ... (1 + (s.toNat-j2nat-1)) (0+j2nat) (radix4Inner ... j2nat 0 a)
    rw [show (0 : ℕ) + j2nat = j2nat from Nat.zero_add j2nat]
    -- Now split (1 + rest) = 1 + (s.toNat-j2nat-1), starting at j2nat
    rw [radix4Inner_comp]
    -- Second split: radix4Inner ... (s.toNat-j2nat-1) (j2nat+1) (... 1 j2nat (... j2nat 0 a))
    -- And radix4Inner ... 1 j2nat A = butterfly4 A false roots s.toNat len.toNat i2.toNat j2u.toNat
    have h_inner1 :
        radix4Inner false roots s.toNat len.toNat i2.toNat 1 j2nat
            (radix4Inner false roots s.toNat len.toNat i2.toNat j2nat 0 a) =
        butterfly4 (radix4Inner false roots s.toNat len.toNat i2.toNat j2nat 0 a)
            false roots s.toNat len.toNat i2.toNat j2u.toNat := by
      simp only [radix4Inner, hj2u_toNat]
    simp only [← hs_split]
    rw [h_inner1]
  -- Generic position formulas for any j2 < 2^q, via ntt_block_pos_arith_nat
  have h_pos0_gen : ∀ j2 : ℕ, j2 < 2 ^ q →
      (i2 + j2.toUInt64).toNat = b * 2 ^ (q + 2) + j2 :=
    fun j2 hj2 => (ntt_block_pos_arith_nat n q hq2 hm_eq hn64 len hlen b j2 hb_pow hj2).2.1
  have h_pos1_gen : ∀ j2 : ℕ, j2 < 2 ^ q →
      (i2 + j2.toUInt64 + s).toNat = b * 2 ^ (q + 2) + j2 + 2 ^ q :=
    fun j2 hj2 => (ntt_block_pos_arith_nat n q hq2 hm_eq hn64 len hlen b j2 hb_pow hj2).2.2.1
  have h_pos2_gen : ∀ j2 : ℕ, j2 < 2 ^ q →
      (i2 + len + j2.toUInt64).toNat = b * 2 ^ (q + 2) + j2 + 2 ^ (q + 1) :=
    fun j2 hj2 => (ntt_block_pos_arith_nat n q hq2 hm_eq hn64 len hlen b j2 hb_pow hj2).2.2.2.1
  have h_pos3_gen : ∀ j2 : ℕ, j2 < 2 ^ q →
      (i2 + len + j2.toUInt64 + s).toNat = b * 2 ^ (q + 2) + j2 + 2 ^ (q + 1) + 2 ^ q :=
    fun j2 hj2 => (ntt_block_pos_arith_nat n q hq2 hm_eq hn64 len hlen b j2 hb_pow hj2).2.2.2.2.1
  have h_bnd_gen : ∀ j2 : ℕ, j2 < 2 ^ q →
      (i2 + j2.toUInt64).toNat < m ∧ (i2 + j2.toUInt64 + s).toNat < m ∧
      (i2 + len + j2.toUInt64).toNat < m ∧ (i2 + len + j2.toUInt64 + s).toNat < m := by
    intro j2 hj2
    obtain ⟨_, _, _, _, _, h5, h6, h7, h8⟩ :=
      ntt_block_pos_arith_nat n q hq2 hm_eq hn64 len hlen b j2 hb_pow hj2
    exact ⟨h5, h6, h7, h8⟩
  -- Show that, for any j2 ≠ j2nat in [0, 2^q), the four positions touched by
  -- the butterfly at j2 are different from any of the 4 idx-positions
  -- corresponding to quad ∈ {0,1,2,3}.
  -- The key arithmetic fact: x + j2nat = y + j2 forces j2nat = j2 mod 2^q
  -- (under bounded conditions).
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
      (radix4Inner false roots s.toNat len.toNat i2.toNat nsteps start B)[posval]'hbnd =
          B[posval]'hbnd := by
    intro B nsteps start posval hbnd hpos hlt_range hne
    apply radix4Inner_getElem_ne roots B s.toNat len.toNat i2.toNat nsteps start posval hbnd
    · intro j2 hlo hhi
      obtain ⟨hb0, hb1, hb2, hb3⟩ := h_bnd_gen j2 (hlt_range j2 hlo hhi)
      rw [h_pos0_gen j2 (hlt_range j2 hlo hhi), ← hi2_toNat] at hb0
      rw [h_pos1_gen j2 (hlt_range j2 hlo hhi), ← hi2_toNat, ← hs_eq] at hb1
      rw [h_pos2_gen j2 (hlt_range j2 hlo hhi), ← hi2_toNat] at hb2
      rw [h_pos3_gen j2 (hlt_range j2 hlo hhi), ← hi2_toNat, ← hs_eq] at hb3
      exact ⟨hb0, hb1, by omega, by omega⟩
    · intro j2 hlo hhi
      obtain ⟨hn0, hn1, hn2, hn3⟩ :=
        h_ne_gen j2 (hlt_range j2 hlo hhi) (hne j2 hlo hhi) posval hpos
      rw [h_pos0_gen j2 (hlt_range j2 hlo hhi), ← hi2_toNat] at hn0
      rw [h_pos1_gen j2 (hlt_range j2 hlo hhi), ← hi2_toNat, ← hs_eq] at hn1
      rw [h_pos2_gen j2 (hlt_range j2 hlo hhi), ← hi2_toNat] at hn2
      rw [h_pos3_gen j2 (hlt_range j2 hlo hhi), ← hi2_toNat, ← hs_eq] at hn3
      exact ⟨hn0, hn1, fun h => hn2 (by omega), fun h => hn3 (by omega)⟩
  have h_leading_pos0 := h_ne_at a j2nat 0 _ hbnd0 (Or.inl h_i2_j2_toNat)
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).trans hj2_lt)
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).ne)
  have h_leading_pos1 := h_ne_at a j2nat 0 _ hbnd1 (Or.inr (Or.inl h_i2_j2_s_toNat))
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).trans hj2_lt)
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).ne)
  have h_leading_pos2 :=
    h_ne_at a j2nat 0 _ hbnd2 (Or.inr (Or.inr (Or.inl h_i2_len_j2_toNat)))
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).trans hj2_lt)
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).ne)
  have h_leading_pos3 :=
    h_ne_at a j2nat 0 _ hbnd3 (Or.inr (Or.inr (Or.inr h_i2_len_j2_s_toNat)))
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).trans hj2_lt)
      (fun _ _ hhi => (lt_of_lt_of_eq hhi (Nat.zero_add j2nat)).ne)
  -- Bound used in trailing lambdas: precomputed to avoid omega inside closures
  have h_trail_bound : j2nat + 1 + (s.toNat - j2nat - 1) ≤ 2 ^ q := by
    rw [hs_eq]; exact nat_trail_bound j2nat (2 ^ q) hj2_lt
  have h_trailing_pos0 : ∀ B,
      (radix4Inner false roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
          (j2nat + 1) B)[(i2 + j2u).toNat]'hbnd0 = B[(i2 + j2u).toNat]'hbnd0 :=
    fun B => h_ne_at B _ _ _ hbnd0 (Or.inl h_i2_j2_toNat)
      (fun _ _ hhi => Nat.lt_of_lt_of_le hhi h_trail_bound)
      (fun _ hlo _ => Nat.ne_of_gt (Nat.lt_of_succ_le hlo))
  have h_trailing_pos1 : ∀ B,
      (radix4Inner false roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
          (j2nat + 1) B)[(i2 + j2u + s).toNat]'hbnd1 = B[(i2 + j2u + s).toNat]'hbnd1 :=
    fun B => h_ne_at B _ _ _ hbnd1 (Or.inr (Or.inl h_i2_j2_s_toNat))
      (fun _ _ hhi => Nat.lt_of_lt_of_le hhi h_trail_bound)
      (fun _ hlo _ => Nat.ne_of_gt (Nat.lt_of_succ_le hlo))
  have h_trailing_pos2 : ∀ B,
      (radix4Inner false roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
          (j2nat + 1) B)[(i2 + len + j2u).toNat]'hbnd2 = B[(i2 + len + j2u).toNat]'hbnd2 :=
    fun B => h_ne_at B _ _ _ hbnd2 (Or.inr (Or.inr (Or.inl h_i2_len_j2_toNat)))
      (fun _ _ hhi => Nat.lt_of_lt_of_le hhi h_trail_bound)
      (fun _ hlo _ => Nat.ne_of_gt (Nat.lt_of_succ_le hlo))
  have h_trailing_pos3 : ∀ B,
      (radix4Inner false roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
          (j2nat + 1) B)[(i2 + len + j2u + s).toNat]'hbnd3 = B[(i2 + len + j2u + s).toNat]'hbnd3 :=
    fun B => h_ne_at B _ _ _ hbnd3 (Or.inr (Or.inr (Or.inr h_i2_len_j2_s_toNat)))
      (fun _ _ hhi => Nat.lt_of_lt_of_le hhi h_trail_bound)
      (fun _ hlo _ => Nat.ne_of_gt (Nat.lt_of_succ_le hlo))
  -- Apply butterfly4_forward_ZMod_combined to the leading vector.
  set A_lead := radix4Inner false roots s.toNat len.toNat i2.toNat j2nat 0 a with hA_lead_def
  have hA_lead_bnd : A_lead.all (· < mod32) := by
    rw [hA_lead_def]
    exact radix4Inner_bound false roots s.toNat len.toNat i2.toNat j2nat 0 a ha_bnd
  -- UInt64-to-ℕ index equalities, defined here so hbnd0'-3' can use them directly.
  -- Using hpos_eqK ▸ hbndK ensures that simp only [← hpos_eqK] cancels back to exactly hbndK,
  -- avoiding fat proof terms that cause expensive isDefEq proof-irrelevance checks later.
  have hpos_eq0 : (i2 + j2u).toNat = i2.toNat + j2u.toNat := by
    rw [h_i2_j2_toNat, hi2_toNat, hj2u_toNat]
  have hpos_eq1 : (i2 + j2u + s).toNat = i2.toNat + j2u.toNat + s.toNat := by
    rw [h_i2_j2_s_toNat, hi2_toNat, hj2u_toNat, hs_eq]
  have hpos_eq2 : (i2 + len + j2u).toNat = i2.toNat + len.toNat + j2u.toNat := by
    rw [h_i2_len_j2_toNat, hi2_toNat, hj2u_toNat, hlen]; ring
  have hpos_eq3 : (i2 + len + j2u + s).toNat = i2.toNat + len.toNat + j2u.toNat + s.toNat := by
    rw [h_i2_len_j2_s_toNat, hi2_toNat, hj2u_toNat, hs_eq, hlen]; ring
  have hpos_eq01 : (i2 + j2u).toNat + s.toNat = (i2 + j2u + s).toNat := by
    rw [h_i2_j2_toNat, h_i2_j2_s_toNat, hs_eq]
  have hpos_eq21 : (i2 + len + j2u).toNat + s.toNat = (i2 + len + j2u + s).toNat := by
    rw [h_i2_len_j2_toNat, h_i2_len_j2_s_toNat, hs_eq]
  -- Convert UInt64-phrased bounds to ℕ-arithmetic form for butterfly4_forward_ZMod_combined
  have hbnd0' : i2.toNat + j2u.toNat < m := hpos_eq0 ▸ hbnd0
  have hbnd1' : i2.toNat + j2u.toNat + s.toNat < m := hpos_eq1 ▸ hbnd1
  have hbnd2' : i2.toNat + len.toNat + j2u.toNat < m := hpos_eq2 ▸ hbnd2
  have hbnd3' : i2.toNat + len.toNat + j2u.toNat + s.toNat < m := hpos_eq3 ▸ hbnd3
  have hbf := butterfly4_forward_ZMod_combined roots A_lead hA_lead_bnd hroots hroots_bnd
    s.toNat len.toNat i2.toNat j2u.toNat hlen_butterfly hdvd hj2_lt_s
    hbnd0' hbnd1' hbnd2' hbnd3' hN_le
  obtain ⟨hbf0, hbf2, hbf1, hbf3⟩ := hbf
  -- Substitute h_leading_posK in the A_k expressions: A_lead[posK] = a[posK]
  -- Compute A_k values via h_inv_k
  -- Setup ωq and ω_top abbreviations
  set ωq : ZMod mod32.toNat :=
    (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ q) with hωq_def
  set ω_top : ZMod mod32.toNat :=
    (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ (q + 2)) with hω_top_def
  -- ω_top^4 = ωq because 2^(q+2) ∣ mod64-1
  have h_dvd_q2 : 2 ^ (q + 2) ∣ mod64.toNat - 1 :=
    dvd_trans (pow_dvd_pow 2 hq2) h_dvd
  have h_div_4 : 4 * ((mod64.toNat - 1) / 2 ^ (q + 2)) = (mod64.toNat - 1) / 2 ^ q := by
    obtain ⟨K, hK⟩ := h_dvd_q2
    have hpos : (2 : ℕ) ^ (q + 2) > 0 := Nat.two_pow_pos _
    have hpos_q : (2 : ℕ) ^ q > 0 := Nat.two_pow_pos _
    have h_pow_eq : (2 : ℕ) ^ (q + 2) = 4 * 2 ^ q := by ring
    rw [hK, Nat.mul_div_cancel_left _ hpos, h_pow_eq]
    rw [(by ring : 4 * 2 ^ q * K = 2 ^ q * (4 * K)),
        Nat.mul_div_cancel_left _ hpos_q]
  have h_omega_q : ω_top ^ 4 = ωq := by
    rw [hωq_def, hω_top_def, ← pow_mul]
    congr 1
    rw [(by ring : (mod64.toNat - 1) / 2 ^ (q + 2) * 4 = 4 * ((mod64.toNat - 1) / 2 ^ (q + 2))),
        h_div_4]
  -- Express τ₁, τ₂, τ₃ in terms of ω_top
  have h_tau2 : (primRoot.toNat : ZMod mod32.toNat) ^
      ((mod64.toNat - 1) / (2 * len.toNat) * j2u.toNat) = ω_top ^ j2nat := by
    rw [hω_top_def, ← pow_mul, hj2u_toNat]
    congr 1
    rw [hlen, (by ring : 2 * 2 ^ (q + 1) = 2 ^ (q + 2))]
  have h_tau3 : (primRoot.toNat : ZMod mod32.toNat) ^
      ((mod64.toNat - 1) / (2 * len.toNat) * (s.toNat + j2u.toNat)) = ω_top ^ (2 ^ q + j2nat) := by
    rw [hω_top_def, ← pow_mul, hj2u_toNat, hs_eq]
    congr 1
    rw [hlen, (by ring : 2 * 2 ^ (q + 1) = 2 ^ (q + 2))]
  have h_tau1 : (primRoot.toNat : ZMod mod32.toNat) ^
      ((mod64.toNat - 1) / len.toNat * j2u.toNat) = (ω_top ^ 2) ^ j2nat := by
    rw [← pow_mul, hω_top_def, ← pow_mul, hj2u_toNat]
    congr 1
    obtain ⟨K, hK⟩ := h_dvd_q2
    have hpos : (2 : ℕ) ^ (q + 2) > 0 := Nat.two_pow_pos _
    have hpos1 : (2 : ℕ) ^ (q + 1) > 0 := Nat.two_pow_pos _
    have h_eq : (2 : ℕ) ^ (q + 2) = 2 * 2 ^ (q + 1) := by ring
    rw [hlen, hK, Nat.mul_div_cancel_left _ hpos, h_eq]
    rw [(by ring : 2 * 2 ^ (q + 1) * K = 2 ^ (q + 1) * (2 * K)),
        Nat.mul_div_cancel_left _ hpos1]
    ring
  -- Compute A₀ via h_inv_k and ntt_sub_input_block_0
  have hb_pow' : b < 2 ^ (n - q - 2) := hb_pow
  have h_idx_in_bnd : ∀ k, k < 4 → (4 * b + k) * 2 ^ q + j2nat < m := by
    intro k hk
    rw [hm_eq]
    have hpow_e : 2 ^ (q + 2) = 4 * 2 ^ q := by ring
    have h_decomp : (4 * b + k) * 2 ^ q + j2nat = b * 2 ^ (q + 2) + (k * 2 ^ q + j2nat) := by
      rw [Nat.add_mul, hpow_e]; ring
    rw [h_decomp]
    have hk3 : k ≤ 3 := Nat.lt_succ_iff.mp hk
    have hpow : k * 2 ^ q + j2nat < 2 ^ (q + 2) := by
      rw [hpow_e]
      calc k * 2 ^ q + j2nat
          ≤ 3 * 2 ^ q + j2nat := Nat.add_le_add_right (Nat.mul_le_mul_right _ hk3) _
        _ < 3 * 2 ^ q + 2 ^ q := Nat.add_lt_add_left hj2_lt _
        _ = 4 * 2 ^ q := by ring
    calc b * 2 ^ (q + 2) + (k * 2 ^ q + j2nat)
        < b * 2 ^ (q + 2) + 2 ^ (q + 2) := Nat.add_lt_add_left hpow _
      _ = (b + 1) * 2 ^ (q + 2) := by ring
      _ ≤ 2 ^ n := hbp1
  -- A-values from h_inv_k
  have hq_sub_le : q ≤ n := by omega
  have hidx0 := h_idx_in_bnd 0 (by decide)
  have hidx1 := h_idx_in_bnd 1 (by decide)
  have hidx2 := h_idx_in_bnd 2 (by decide)
  have hidx3 := h_idx_in_bnd 3 (by decide)
  have hA0_eq : ((A_lead[(i2 + j2u).toNat]'hbnd0).toNat : ZMod mod32.toNat) =
      ref_ntt q ωq (ntt_sub_input n q hq_sub_le hm_eq v (4 * b + 0)) ⟨j2nat, hj2_lt⟩ := by
    rw [h_leading_pos0]
    have heq : a[(i2 + j2u).toNat]'hbnd0 = a[(4 * b + 0) * 2 ^ q + j2nat]'hidx0 :=
      getElem_congr_idx hpos0_match
    rw [heq]; exact h_inv_k 0 (by decide) ⟨j2nat, hj2_lt⟩ hidx0
  have hA1_eq : ((A_lead[(i2 + j2u + s).toNat]'hbnd1).toNat : ZMod mod32.toNat) =
      ref_ntt q ωq (ntt_sub_input n q hq_sub_le hm_eq v (4 * b + 1)) ⟨j2nat, hj2_lt⟩ := by
    rw [h_leading_pos1]
    have heq : a[(i2 + j2u + s).toNat]'hbnd1 = a[(4 * b + 1) * 2 ^ q + j2nat]'hidx1 :=
      getElem_congr_idx hpos1_match
    rw [heq]; exact h_inv_k 1 (by decide) ⟨j2nat, hj2_lt⟩ hidx1
  have hA2_eq : ((A_lead[(i2 + len + j2u).toNat]'hbnd2).toNat : ZMod mod32.toNat) =
      ref_ntt q ωq (ntt_sub_input n q hq_sub_le hm_eq v (4 * b + 2)) ⟨j2nat, hj2_lt⟩ := by
    rw [h_leading_pos2]
    have heq : a[(i2 + len + j2u).toNat]'hbnd2 = a[(4 * b + 2) * 2 ^ q + j2nat]'hidx2 :=
      getElem_congr_idx hpos2_match
    rw [heq]; exact h_inv_k 2 (by decide) ⟨j2nat, hj2_lt⟩ hidx2
  have hA3_eq : ((A_lead[(i2 + len + j2u + s).toNat]'hbnd3).toNat : ZMod mod32.toNat) =
      ref_ntt q ωq (ntt_sub_input n q hq_sub_le hm_eq v (4 * b + 3)) ⟨j2nat, hj2_lt⟩ := by
    rw [h_leading_pos3]
    have heq : a[(i2 + len + j2u + s).toNat]'hbnd3 = a[(4 * b + 3) * 2 ^ q + j2nat]'hidx3 :=
      getElem_congr_idx hpos3_match
    rw [heq]; exact h_inv_k 3 (by decide) ⟨j2nat, hj2_lt⟩ hidx3
  -- Use ntt_sub_input_block_K to rewrite the ntt_sub_input expressions in terms of v at b
  -- Define the f function for ref_ntt at level q+2:
  set f_ntt : Fin (2 ^ (q + 2)) → ZMod mod32.toNat :=
    ntt_sub_input n (q + 2) hq2 hm_eq v b with hf_ntt_def
  have h_sub0_fun : ntt_sub_input n q hq_sub_le hm_eq v (4 * b + 0) =
      fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val, fin_4mul_lt q j⟩ := by
    funext j; rw [hf_ntt_def]
    exact ntt_sub_input_block_0 n q hq2 hm_eq v b hb_pow' j
  have h_sub1_fun : ntt_sub_input n q hq_sub_le hm_eq v (4 * b + 1) =
      fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 2, fin_4mul2_lt q j⟩ := by
    funext j; rw [hf_ntt_def]
    exact ntt_sub_input_block_1 n q hq2 hm_eq v b j
  have h_sub2_fun : ntt_sub_input n q hq_sub_le hm_eq v (4 * b + 2) =
      fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 1, fin_4mul1_lt q j⟩ := by
    funext j; rw [hf_ntt_def]
    exact ntt_sub_input_block_2 n q hq2 hm_eq v b j
  have h_sub3_fun : ntt_sub_input n q hq_sub_le hm_eq v (4 * b + 3) =
      fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 3, fin_4mul3_lt q j⟩ := by
    funext j; rw [hf_ntt_def]
    exact ntt_sub_input_block_3 n q hq2 hm_eq v b hb_pow' j
  have hA0_final : ((A_lead[(i2 + j2u).toNat]'hbnd0).toNat : ZMod mod32.toNat) =
      ref_ntt q (ω_top ^ 4)
        (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val, fin_4mul_lt q j⟩) ⟨j2nat, hj2_lt⟩ := by
    rw [hA0_eq, h_omega_q, ← h_sub0_fun]
  have hA1_final : ((A_lead[(i2 + j2u + s).toNat]'hbnd1).toNat : ZMod mod32.toNat) =
      ref_ntt q (ω_top ^ 4)
        (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 2, fin_4mul2_lt q j⟩)
        ⟨j2nat, hj2_lt⟩ := by
    rw [hA1_eq, h_omega_q, ← h_sub1_fun]
  have hA2_final : ((A_lead[(i2 + len + j2u).toNat]'hbnd2).toNat : ZMod mod32.toNat) =
      ref_ntt q (ω_top ^ 4)
        (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 1, fin_4mul1_lt q j⟩)
        ⟨j2nat, hj2_lt⟩ := by
    rw [hA2_eq, h_omega_q, ← h_sub2_fun]
  have hA3_final : ((A_lead[(i2 + len + j2u + s).toNat]'hbnd3).toNat : ZMod mod32.toNat) =
      ref_ntt q (ω_top ^ 4)
        (fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 3, fin_4mul3_lt q j⟩)
        ⟨j2nat, hj2_lt⟩ := by
    rw [hA3_eq, h_omega_q, ← h_sub3_fun]
  -- Convert hbfK indices to UInt64-form and substitute A_lead with ref_ntt values,
  -- then delegate the 4-way case split to a helper with a small local context.
  simp only [hpos_eq01, hpos_eq21, ← hpos_eq0, ← hpos_eq2,
             hA0_final, hA1_final, hA2_final, hA3_final] at hbf0 hbf1 hbf2 hbf3
  exact radix4Inner_case_split q b r j2nat quad hp hj2_lt hquad_lt hr_decomp hidx
    i2 j2u s len ω_top f_ntt A_lead roots a
    hbnd0 hbnd1 hbnd2 hbnd3
    h_i2_j2_toNat h_i2_j2_s_toNat h_i2_len_j2_toNat h_i2_len_j2_s_toNat
    h_split h_trailing_pos0 h_trailing_pos1 h_trailing_pos2 h_trailing_pos3
    hbf0 hbf1 hbf2 hbf3
    h_tau1 h_tau2 h_tau3
