/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib
import UniversalHashing.BinConvolution.ConvolutionHelpers.DFTLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.SolutionHelpers
import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpers
import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpersInverseNTT
import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpersInv
import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpersForward



/-!
# Inverse NTT outer-loop: radix4Middle advance, outerLoop induction

Mirrors `OuterLoopHelpersForward` for the inverse pass (`inverse = true`).
-/

/-- When `outerLoop_inv_inverse` holds at q = n, the array computes the DFT with ω⁻¹. -/
lemma inv_at_n_implies_ref_ntt_inverse {m : ℕ} (n : ℕ)
    (hm_eq : m = 2 ^ n)
    (v : Vector UInt32 m)
    (a : Vector UInt32 m)
    (hinv : outerLoop_inv_inverse n n (le_refl n) hm_eq v a) :
    let ω : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)
    ∀ k : Fin m,
      ((a[k.val]).toNat : ZMod mod32.toNat) =
        ref_ntt n ω⁻¹
          (fun j : Fin (2 ^ n) => ((v[Fin.cast hm_eq.symm j]).toNat : ZMod mod32.toNat))
          (Fin.cast hm_eq k) := by
  have hthis := hinv.2 0
  simp only [Nat.sub_self, pow_zero, Nat.zero_mul, Nat.zero_add, hm_eq,
             show (0:ℕ) < 1 from Nat.one_pos, forall_const,
             Fin.is_lt, forall_prop_of_true] at hthis ⊢
  convert hthis using 1
  constructor <;> intro h r <;>
    specialize h ⟨r, by linarith [Fin.is_lt r, hm_eq]⟩ <;>
    simp_all +decide only [Fin.getElem_fin, Fin.val_cast]
  unfold ntt_sub_input_inv; simp +decide [Fin.cast]

lemma radix4Middle_advances_inv_inverse {m : ℕ} (n q : ℕ) (hq2 : q + 2 ≤ n)
    (hm_eq : m = 2 ^ n)
    (v : Vector UInt32 m)
    (roots : Vector UInt32 m)
    (hroots : ntt_roots_correct m roots)
    (hroots_bnd : roots.all (· < mod32))
    (h_dvd : 2 ^ n ∣ mod64.toNat - 1)
    (a : Vector UInt32 m)
    (hinv : outerLoop_inv_inverse n q (by omega) hm_eq v a)
    (len : UInt64) (hlen : len.toNat = 2 ^ (q + 1)) :
    let s := len >>> 1
    outerLoop_inv_inverse n (q + 2) hq2 hm_eq v
      (radix4Middle true roots s.toNat len.toNat (m / (2 * len.toNat)) 0 a) := by
  haveI hp : Fact (Nat.Prime mod32.toNat) := ⟨prime_3221225473⟩
  constructor
  · -- Boundedness
    exact radix4Middle_bound true roots (len >>> 1).toNat len.toNat _ 0 a hinv.1
  · -- Value correctness
    intro b r hb idx hidx
    have hn64 : n < 64 := n_lt_64_of_pow2_nat m n hm_eq (hm_eq.symm ▸ h_dvd)
    have hs_eq : (len >>> 1).toNat = 2 ^ q := by
      simp [UInt64.toNat_shiftRight, hlen, Nat.shiftRight_eq_div_pow, Nat.pow_succ']
    set s : UInt64 := len >>> 1 with hs_def
    have hlen_butterfly : len.toNat = 2 * s.toNat := by rw [hs_eq, hlen]; ring
    have hnBlocks_eq : m / (2 * len.toNat) = 2 ^ (n - q - 2) := by
      rw [hm_eq, hlen, show (2 : ℕ) * 2 ^ (q + 1) = 2 ^ (q + 2) from by ring]
      have h2 : (2 : ℕ) ^ n = 2 ^ (n - q - 2) * 2 ^ (q + 2) := by
        rw [← pow_add]; congr 1; omega
      rw [h2, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    set j2nat : ℕ := r.val % 2 ^ q
    set quad : ℕ := r.val / 2 ^ q
    have hj2_lt : j2nat < 2 ^ q := Nat.mod_lt _ (Nat.two_pow_pos q)
    have hquad_lt : quad < 4 := by
      have hrlt : r.val < 4 * 2 ^ q := by
        have := r.isLt; linarith [show (2:ℕ)^(q+2) = 4 * 2^q from by ring]
      exact Nat.div_lt_iff_lt_mul (Nat.two_pow_pos q) |>.mpr (by linarith)
    have hb_pow : b < 2 ^ (n - q - 2) := (show n - (q + 2) = n - q - 2 by omega) ▸ hb
    have h_i2nat : ((b * 2 * len.toNat).toUInt64).toNat = b * 2 * len.toNat :=
      nat_toUInt64_faithful _ (by
        calc b * 2 * len.toNat = b * 2 ^ (q + 2) := by rw [hlen]; ring
          _ < 2 ^ (n - q - 2) * 2 ^ (q + 2) := (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hb_pow
          _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
          _ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hn64)
    have hb4_lt : ∀ k < 4, 4 * b + k < 2 ^ (n - q) := by
      intro k hk
      have h4 : 4 * 2 ^ (n - q - 2) = 2 ^ (n - q) := by
        rw [show (4:ℕ) = 2^2 from by norm_num, ← pow_add]; congr 1; omega
      nlinarith [Nat.mul_lt_mul_of_pos_left hb_pow (show 0 < 4 by decide)]
    set ωq_inv : ZMod mod32.toNat :=
      (((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ q))⁻¹)
    set nBlocks : ℕ := m / (2 * len.toNat)
    have hb_lt_nBlocks : b < nBlocks := by rw [hnBlocks_eq]; exact hb_pow
    have hbnd_all : ∀ b' < nBlocks, (b' + 1) * 2 * len.toNat ≤ m := fun b' hb' => by
      have hb'_pow : b' < 2 ^ (n - q - 2) := hnBlocks_eq ▸ hb'
      calc (b' + 1) * 2 * len.toNat = (b' + 1) * 2 ^ (q + 2) := by rw [hlen]; ring
        _ ≤ 2 ^ (n - q - 2) * 2 ^ (q + 2) := Nat.mul_le_mul_right _ hb'_pow
        _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
        _ = m := hm_eq.symm
    have hlen_2s : 2 * s.toNat ≤ len.toNat := by linarith [hlen_butterfly]
    have h_idx_lo : b * 2 * len.toNat ≤ idx := by
      change b * 2 * len.toNat ≤ b * 2 ^ (q + 2) + r.val
      have : b * 2 * len.toNat = b * 2 ^ (q + 2) := by rw [hlen]; ring
      linarith [Nat.zero_le r.val]
    have h_idx_hi : idx < (b + 1) * 2 * len.toNat := by
      change b * 2 ^ (q + 2) + r.val < (b + 1) * 2 * len.toNat
      have : (b + 1) * 2 * len.toNat = (b + 1) * 2 ^ (q + 2) := by rw [hlen]; ring
      linarith [r.isLt]
    set a_mid := radix4Middle true roots s.toNat len.toNat b 0 a
    -- Steps A+B: reduce full radix4Middle at idx to radix4Inner on a_mid
    have h_eq : (radix4Middle true roots s.toNat len.toNat nBlocks 0 a)[idx]'hidx =
        (radix4Inner true roots s.toNat len.toNat (b * 2 * len.toNat) s.toNat 0
          a_mid)[idx]'hidx := by
      apply radix4Middle_getElem_at_block
      · exact hb_lt_nBlocks
      · exact hlen_2s
      · exact hbnd_all
      · exact h_idx_hi
    -- Step C: leading b blocks don't touch positions (4*b+k)*2^q + j2.val
    have h_inv_k_mid : ∀ k, k < 4 → ∀ (j2 : Fin (2 ^ q))
        (hidx_k : (4 * b + k) * 2 ^ q + j2.val < m),
        ((a_mid[(4 * b + k) * 2 ^ q + j2.val]'hidx_k).toNat : ZMod mod32.toNat) =
          ref_ntt q ωq_inv (ntt_sub_input_inv n q (by omega) hm_eq v (4 * b + k)) j2 := by
      intro k hk j2 hidx_k
      have h_target_ge : b * 2 * len.toNat ≤ (4 * b + k) * 2 ^ q + j2.val := by
        rw [hlen]; nlinarith [Nat.two_pow_pos q, Nat.zero_le (k * 2^q + j2.val)]
      rw [radix4Middle_leading_getElem_eq true roots a s.toNat len.toNat b hlen_2s
            (fun b'' hb'' => hbnd_all b'' (lt_trans hb'' hb_lt_nBlocks)) _ hidx_k h_target_ge]
      exact hinv.2 (4 * b + k) j2 (hb4_lt k hk) hidx_k
    -- Step D: a_mid is bounded by mod32
    have ha_mid_bnd : a_mid.all (· < mod32) :=
      radix4Middle_bound true roots s.toNat len.toNat b 0 a hinv.1
    -- Step E: apply radix4Inner_single_block_correct_inv
    have h_inner :=
      radix4Inner_single_block_correct_inv (m := m) n q hq2 hm_eq v roots hroots hroots_bnd
        h_dvd (hm_eq ▸ h_dvd) a_mid ha_mid_bnd len hlen b hb h_inv_k_mid r hidx
    simp only at h_inner
    rw [h_eq, ← h_i2nat]
    exact h_inner

lemma outerLoop_from_inv_inverse {m : ℕ} (n q : ℕ)
    (hm_eq : m = 2 ^ n)
    (v : Vector UInt32 m)
    (roots : Vector UInt32 m)
    (hroots : ntt_roots_correct m roots)
    (hroots_bnd : roots.all (· < mod32))
    (h_dvd : 2 ^ n ∣ mod64.toNat - 1)
    (a : Vector UInt32 m)
    (hq : q ≤ n)
    (hinv : outerLoop_inv_inverse n q hq hm_eq v a)
    (len : UInt64)
    (hlen : len.toNat = 2 ^ (q + 1))
    (hq_even : Even (n - q))
    (fuel : ℕ) (hfuel : n ≤ q + 2 * fuel) :
    let ω : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)
    ∀ k : Fin m,
      ((nttInplace.outerLoop true roots a len fuel)[k.val].toNat : ZMod mod32.toNat) =
        ref_ntt n ω⁻¹
          (fun j : Fin (2 ^ n) => ((v[Fin.cast hm_eq.symm j]).toNat : ZMod mod32.toNat))
          (Fin.cast hm_eq k) := by
  haveI hp : Fact (Nat.Prime mod32.toNat) := ⟨prime_3221225473⟩
  simp only
  intro k
  induction fuel generalizing q a len with
  | zero =>
    have hqn : q = n := by omega
    cases hqn
    simp only [nttInplace.outerLoop]
    exact inv_at_n_implies_ref_ntt_inverse n hm_eq v a hinv k
  | succ fuel ih =>
    by_cases hqn : q = n
    · cases hqn
      have hn64 : n < 64 := n_lt_64_of_pow2_nat m n hm_eq (hm_eq.symm ▸ h_dvd)
      have hn1_64 : n + 1 < 64 := by
        have := len.toNat_lt; rw [hlen] at this
        exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp this
      have h_noop := outerLoop_noop_pow2 true roots a len (fuel + 1) n hm_eq
        (Or.inl ⟨n + 1, hlen, Nat.lt_succ_of_le le_rfl, hn1_64⟩)
      rw [h_noop]
      exact inv_at_n_implies_ref_ntt_inverse n hm_eq v a hinv k
    · have hq_lt : q < n := lt_of_le_of_ne hq hqn
      have hq2 : q + 2 ≤ n := by
        obtain ⟨d, hd⟩ := hq_even; omega
      have hn64 : n < 64 := n_lt_64_of_pow2_nat m n hm_eq (hm_eq.symm ▸ h_dvd)
      have hgt_neg : ¬(len.toNat * 2 > m) :=
        outerLoop_len_not_gt_nat n q hm_eq hq2 len hlen
      simp only [nttInplace.outerLoop, hgt_neg, ↓reduceIte]
      have hinv' :=
        radix4Middle_advances_inv_inverse n q hq2 hm_eq v roots hroots hroots_bnd
          h_dvd a hinv len hlen
      by_cases hq2n : q + 2 = n
      · have hinv_n : outerLoop_inv_inverse n n (le_refl n) hm_eq v
            (radix4Middle true roots (len >>> 1).toNat len.toNat (m / (2 * len.toNat)) 0 a) := by
          convert hinv' using 1
          omega
        have h_noop := outerLoop_noop_pow2 true roots
          (radix4Middle true roots (len >>> 1).toNat len.toNat (m / (2 * len.toNat)) 0 a)
          (len <<< 2) fuel n hm_eq
        by_cases hq3_strict : q + 3 < 64
        · have hlen' := outerLoop_len_shift q len hlen (by omega)
          have h1 : (len <<< 2).toNat = 2 ^ (q + 3) := hlen'
          have h2 := h_noop (Or.inl ⟨q + 3, h1, by omega, hq3_strict⟩)
          simp only [h2]
          exact inv_at_n_implies_ref_ntt_inverse n hm_eq v _ hinv_n k
        · have hlen_shift_zero : (len <<< 2).toNat = 0 := by
            simp only [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat, hlen, Nat.shiftLeft_eq]
            norm_num
            have hq_ge : q ≥ 61 := by omega
            have hq_le : q ≤ 62 := by omega
            interval_cases q <;> norm_num
          have h2 := h_noop (Or.inr hlen_shift_zero)
          simp only [h2]
          exact inv_at_n_implies_ref_ntt_inverse n hm_eq v _ hinv_n k
      · have hq2_lt : q + 2 < n := by omega
        have hlen' : (len <<< 2).toNat = 2 ^ (q + 2 + 1) :=
          outerLoop_len_shift q len hlen (by omega)
        have heven' : Even (n - (q + 2)) := by
          obtain ⟨d, hd⟩ := hq_even; exact ⟨d - 1, by omega⟩
        exact ih (q + 2)
          (radix4Middle true roots (len >>> 1).toNat len.toNat (m / (2 * len.toNat)) 0 a)
          hq2 hinv' (len <<< 2) hlen' heven' (by omega)
