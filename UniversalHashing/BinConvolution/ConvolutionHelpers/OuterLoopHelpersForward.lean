/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib
import UniversalHashing.BinConvolution.ConvolutionHelpers.DFTLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.MontgomeryLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.RootTableLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.NttBoundLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.Radix4ForwardLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpers
import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpersRadix4Inner
import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpersInverseNTT


/-!
# Forward NTT outer-loop: radix4Middle, outerLoop, bit-reversal, preprocessing

This file contains the larger forward-pass outer-loop lemmas split out from `OuterLoopHelpers`
to keep per-file elaboration memory bounded.
-/

/-- Position arithmetic for a generic block `b'` in a radix-4 pass at level `q`. -/
lemma block_positions_arithmetic (n q : ℕ) (hq2 : q + 2 ≤ n) (hn64 : n < 64)
    (len : UInt64) (hlen : len.toNat = 2 ^ (q + 1))
    (b' : ℕ) (hb'_pow : b' < 2 ^ (n - q - 2))
    (j2 : ℕ) (hj2 : j2 < 2 ^ q) :
    ((b' * 2 * len.toNat).toUInt64).toNat = b' * 2 ^ (q + 2) ∧
    (j2.toUInt64).toNat = j2 ∧
    ((b' * 2 * len.toNat).toUInt64 + j2.toUInt64).toNat = b' * 2 ^ (q + 2) + j2 ∧
    ((b' * 2 * len.toNat).toUInt64 + j2.toUInt64 + (len >>> 1)).toNat =
      b' * 2 ^ (q + 2) + j2 + 2 ^ q ∧
    ((b' * 2 * len.toNat).toUInt64 + len + j2.toUInt64).toNat =
      b' * 2 ^ (q + 2) + j2 + 2 ^ (q + 1) ∧
    ((b' * 2 * len.toNat).toUInt64 + len + j2.toUInt64 + (len >>> 1)).toNat =
      b' * 2 ^ (q + 2) + j2 + 2 ^ (q + 1) + 2 ^ q ∧
    (b' + 1) * 2 ^ (q + 2) ≤ 2 ^ n := by
  have hs_eq : (len >>> 1).toNat = 2 ^ q := by
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, hlen, Nat.pow_succ',
               (by decide : (1 : UInt64).toNat % 64 = 1), pow_one]; omega
  have hb'_i2_lt : b' * 2 ^ (q + 2) < 2 ^ n := by
    have : b' * 2 ^ (q + 2) < 2 ^ (n - q - 2) * 2 ^ (q + 2) := by
      nlinarith [Nat.two_pow_pos (q + 2), hb'_pow]
    rwa [show (2 : ℕ) ^ (n - q - 2) * 2 ^ (q + 2) = 2 ^ n by
      rw [← pow_add]; congr 1; omega] at this
  have hb'_i2_lt_64 : b' * 2 ^ (q + 2) < 2 ^ 64 :=
    lt_of_lt_of_le hb'_i2_lt (Nat.pow_le_pow_right (by decide) (by omega))
  have hi2'_toNat : ((b' * 2 * len.toNat).toUInt64).toNat = b' * 2 ^ (q + 2) := by
    have h1 : b' * 2 * len.toNat = b' * 2 ^ (q + 2) := by rw [hlen]; ring
    rw [h1]; exact nat_toUInt64_faithful _ hb'_i2_lt_64
  have hj2_lt_64 : j2 < 2 ^ 64 :=
    lt_of_lt_of_le hj2 (Nat.pow_le_pow_right (by decide) (by omega))
  have hj2u_toNat : (j2.toUInt64).toNat = j2 := nat_toUInt64_faithful _ hj2_lt_64
  have hbp1 : (b' + 1) * 2 ^ (q + 2) ≤ 2 ^ n := by
    calc (b' + 1) * 2 ^ (q + 2) ≤ 2 ^ (n - q - 2) * 2 ^ (q + 2) :=
          Nat.mul_le_mul_right _ hb'_pow
      _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
  have hbexpand : (b' + 1) * 2 ^ (q + 2) = b' * 2 ^ (q + 2) + 2 ^ (q + 2) := by ring
  have hpow_e : 2 ^ (q + 2) = 4 * 2 ^ q := by ring
  have hjlt_q2 : j2 < 2 ^ (q + 2) :=
    lt_of_lt_of_le hj2 (Nat.pow_le_pow_right (by decide) (by omega))
  have hjs_lt_q2 : j2 + 2 ^ q < 2 ^ (q + 2) := by omega
  have hjlen_lt_q2 : j2 + 2 ^ (q + 1) < 2 ^ (q + 2) := by
    have h2 : 2 ^ (q + 1) = 2 ^ q + 2 ^ q := by ring
    omega
  have hjlens_lt_q2 : j2 + 2 ^ (q + 1) + 2 ^ q < 2 ^ (q + 2) := by
    have hpow1 : 2 ^ (q + 1) = 2 ^ q + 2 ^ q := by ring
    omega
  have hp0 : ((b' * 2 * len.toNat).toUInt64 + j2.toUInt64).toNat = b' * 2 ^ (q + 2) + j2 := by
    rw [UInt64.toNat_add, hi2'_toNat, hj2u_toNat]
    apply Nat.mod_eq_of_lt
    have h_sum_lt : b' * 2 ^ (q + 2) + j2 < 2 ^ n := by omega
    exact lt_of_lt_of_le h_sum_lt (Nat.pow_le_pow_right (by decide) (by omega))
  have hp1 : ((b' * 2 * len.toNat).toUInt64 + j2.toUInt64 + (len >>> 1)).toNat =
      b' * 2 ^ (q + 2) + j2 + 2 ^ q := by
    rw [UInt64.toNat_add, hp0, hs_eq]
    apply Nat.mod_eq_of_lt
    have h_sum_lt : b' * 2 ^ (q + 2) + j2 + 2 ^ q < 2 ^ n := by omega
    exact lt_of_lt_of_le h_sum_lt (Nat.pow_le_pow_right (by decide) (by omega))
  have hp2 : ((b' * 2 * len.toNat).toUInt64 + len + j2.toUInt64).toNat =
      b' * 2 ^ (q + 2) + j2 + 2 ^ (q + 1) := by
    have hrw : (b' * 2 * len.toNat).toUInt64 + len + j2.toUInt64 =
      ((b' * 2 * len.toNat).toUInt64 + j2.toUInt64) + len := by abel
    rw [hrw, UInt64.toNat_add, hp0, hlen]
    apply Nat.mod_eq_of_lt
    have h_sum_lt : b' * 2 ^ (q + 2) + j2 + 2 ^ (q + 1) < 2 ^ n := by omega
    exact lt_of_lt_of_le h_sum_lt (Nat.pow_le_pow_right (by decide) (by omega))
  have hp3 : ((b' * 2 * len.toNat).toUInt64 + len + j2.toUInt64 + (len >>> 1)).toNat =
      b' * 2 ^ (q + 2) + j2 + 2 ^ (q + 1) + 2 ^ q := by
    rw [UInt64.toNat_add, hp2, hs_eq]
    apply Nat.mod_eq_of_lt
    have h_sum_lt : b' * 2 ^ (q + 2) + j2 + 2 ^ (q + 1) + 2 ^ q < 2 ^ n := by omega
    exact lt_of_lt_of_le h_sum_lt (Nat.pow_le_pow_right (by decide) (by omega))
  exact ⟨hi2'_toNat, hj2u_toNat, hp0, hp1, hp2, hp3, hbp1⟩

lemma radix4Middle_advances_inv {m : ℕ} (n q : ℕ) (hq2 : q + 2 ≤ n)
    (hm_eq : m = 2 ^ n)
    (v : Vector UInt32 m)
    (roots : Vector UInt32 m)
    (hroots : ntt_roots_correct m roots)
    (hroots_bnd : roots.all (· < mod32))
    (h_dvd : 2 ^ n ∣ mod64.toNat - 1)
    (a : Vector UInt32 m)
    (hinv : outerLoop_inv n q (by omega) hm_eq v a)
    (len : UInt64) (hlen : len.toNat = 2 ^ (q + 1)) :
    let s := len >>> 1
    outerLoop_inv n (q + 2) hq2 hm_eq v
      (radix4Middle false roots s.toNat len.toNat (m / (2 * len.toNat)) 0 a) := by
  haveI hp : Fact (Nat.Prime mod32.toNat) := ⟨prime_3221225473⟩
  constructor
  · -- Boundedness: the output stays within mod32
    exact radix4Middle_bound false roots (len >>> 1).toNat len.toNat _ 0 a hinv.1
  · -- Value correctness: each element at level q+2 matches ref_ntt
    intro b r hb idx hidx
    have hn64 : n < 64 := n_lt_64_of_pow2_nat m n hm_eq (hm_eq.symm ▸ h_dvd)
    have hs_eq : (len >>> 1).toNat = 2 ^ q := by
      simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, hlen, Nat.pow_succ',
               (by decide : (1 : UInt64).toNat % 64 = 1), pow_one]; omega
    set s : UInt64 := len >>> 1 with hs_def
    have hlen_butterfly : len.toNat = 2 * s.toNat := by rw [hs_eq, hlen]; ring
    have hnBlocks_eq : m / (2 * len.toNat) = 2 ^ (n - q - 2) := by
      rw [hm_eq, hlen, (by ring : (2 : ℕ) * 2 ^ (q + 1) = 2 ^ (q + 2))]
      have h2 : (2 : ℕ) ^ n = 2 ^ (n - q - 2) * 2 ^ (q + 2) := by
        rw [← pow_add]; congr 1; omega
      rw [h2, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    set j2nat : ℕ := r.val % 2 ^ q
    set quad : ℕ := r.val / 2 ^ q
    have hj2_lt : j2nat < 2 ^ q := Nat.mod_lt _ (Nat.two_pow_pos q)
    have hquad_lt : quad < 4 := by
      have hrlt : r.val < 4 * 2 ^ q := by
        have := r.isLt; linarith [(by ring : (2:ℕ)^(q+2) = 4 * 2^q)]
      exact Nat.div_lt_iff_lt_mul (Nat.two_pow_pos q) |>.mpr (by linarith)
    have hb_pow : b < 2 ^ (n - q - 2) := (show n - (q + 2) = n - q - 2 by omega) ▸ hb
    -- i2.toNat = b * 2 * len.toNat (needed to connect with radix4Inner_single_block_correct)
    have h_i2nat : ((b * 2 * len.toNat).toUInt64).toNat = b * 2 * len.toNat :=
      nat_toUInt64_faithful _ (by
        calc b * 2 * len.toNat = b * 2 ^ (q + 2) := by rw [hlen]; ring
          _ < 2 ^ (n - q - 2) * 2 ^ (q + 2) := (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hb_pow
          _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
          _ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hn64)
    have hb4_lt : ∀ k < 4, 4 * b + k < 2 ^ (n - q) := by
      intro k hk
      have h4 : 4 * 2 ^ (n - q - 2) = 2 ^ (n - q) := by
        rw [(by norm_num : (4:ℕ) = 2^2), ← pow_add]; congr 1; omega
      nlinarith [Nat.mul_lt_mul_of_pos_left hb_pow (show 0 < 4 by decide)]
    set ωq : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ q)
    set nBlocks : ℕ := m / (2 * len.toNat)
    have hb_lt_nBlocks : b < nBlocks := by rw [hnBlocks_eq]; exact hb_pow
    have hbnd_all : ∀ b' < nBlocks, (b' + 1) * 2 * len.toNat ≤ m := fun b' hb' => by
      have hb'_pow : b' < 2 ^ (n - q - 2) := hnBlocks_eq ▸ hb'
      calc (b' + 1) * 2 * len.toNat = (b' + 1) * 2 ^ (q + 2) := by rw [hlen]; ring
        _ ≤ 2 ^ (n - q - 2) * 2 ^ (q + 2) := Nat.mul_le_mul_right _ hb'_pow
        _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
        _ = m := hm_eq.symm
    have hlen_2s : 2 * s.toNat ≤ len.toNat := by linarith [hlen_butterfly]
    -- idx is in block b
    have h_idx_lo : b * 2 * len.toNat ≤ idx := by
      change b * 2 * len.toNat ≤ b * 2 ^ (q + 2) + r.val
      have : b * 2 * len.toNat = b * 2 ^ (q + 2) := by rw [hlen]; ring
      linarith [Nat.zero_le r.val]
    have h_idx_hi : idx < (b + 1) * 2 * len.toNat := by
      change b * 2 ^ (q + 2) + r.val < (b + 1) * 2 * len.toNat
      have : (b + 1) * 2 * len.toNat = (b + 1) * 2 ^ (q + 2) := by rw [hlen]; ring
      linarith [r.isLt]
    set a_mid := radix4Middle false roots s.toNat len.toNat b 0 a
    -- Steps A+B: reduce full radix4Middle at idx to radix4Inner on a_mid
    have h_eq : (radix4Middle false roots s.toNat len.toNat nBlocks 0 a)[idx]'hidx =
        (radix4Inner false roots s.toNat len.toNat (b * 2 * len.toNat) s.toNat 0
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
          ref_ntt q ωq (ntt_sub_input n q (by omega) hm_eq v (4 * b + k)) j2 := by
      intro k hk j2 hidx_k
      have h_target_ge : b * 2 * len.toNat ≤ (4 * b + k) * 2 ^ q + j2.val := by
        rw [hlen]; nlinarith [Nat.two_pow_pos q, Nat.zero_le (k * 2^q + j2.val)]
      rw [radix4Middle_leading_getElem_eq false roots a s.toNat len.toNat b hlen_2s
            (fun b'' hb'' => hbnd_all b'' (lt_trans hb'' hb_lt_nBlocks)) _ hidx_k h_target_ge]
      exact hinv.2 (4 * b + k) j2 (hb4_lt k hk) hidx_k
    -- Step D: a_mid is bounded by mod32
    have ha_mid_bnd : a_mid.all (· < mod32) :=
      radix4Middle_bound false roots s.toNat len.toNat b 0 a hinv.1
    -- Step E: apply radix4Inner_single_block_correct
    have h_inner :=
      radix4Inner_single_block_correct n q hq2 hm_eq (hm_eq.symm ▸ h_dvd)
        v roots hroots hroots_bnd
        h_dvd a_mid ha_mid_bnd len hlen b hb h_inv_k_mid r hidx
    simp only at h_inner
    rw [h_eq, ← h_i2nat]
    exact h_inner

/-
When `len.toNat = 2^(q+1)` and `q + 3 < 64`, shifting left by 2 gives `2^(q+3)`.
-/
lemma outerLoop_len_shift (q : ℕ)
    (len : UInt64) (hlen : len.toNat = 2 ^ (q + 1)) (hq3 : q + 2 + 1 < 64) :
    (len <<< 2).toNat = 2 ^ (q + 2 + 1) := by
  norm_num [Nat.pow_succ', Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, hlen]
  have := Nat.le_of_lt_succ (show q < 61 by linarith) ; interval_cases q <;> trivial

lemma outerLoop_from_inv {m : ℕ} (n q : ℕ)
    (hm_eq : m = 2 ^ n)
    (v : Vector UInt32 m)
    (roots : Vector UInt32 m)
    (hroots : ntt_roots_correct m roots)
    (hroots_bnd : roots.all (· < mod32))
    (h_dvd : 2 ^ n ∣ mod64.toNat - 1)
    (a : Vector UInt32 m)
    (hq : q ≤ n)
    (hinv : outerLoop_inv n q hq hm_eq v a)
    (len : UInt64)
    (hlen : len.toNat = 2 ^ (q + 1))
    (hq_even : Even (n - q))
    (fuel : ℕ) (hfuel : n ≤ q + 2 * fuel) :
    let ω : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)
    ∀ k : Fin m,
      ((nttInplace.outerLoop false roots a len fuel)[k.val].toNat : ZMod mod32.toNat) =
        ref_ntt n ω
          (fun j : Fin (2 ^ n) => ((toMont (v[Fin.cast hm_eq.symm j])).toNat : ZMod mod32.toNat))
          (Fin.cast hm_eq k) := by
  haveI hp : Fact (Nat.Prime mod32.toNat) := ⟨prime_3221225473⟩
  simp only
  intro k
  induction fuel generalizing q a len with
  | zero =>
    have hqn : q = n := by omega
    cases hqn
    simp only [nttInplace.outerLoop]
    exact inv_at_n_implies_ref_ntt n hm_eq v a hinv k
  | succ fuel ih =>
    by_cases hqn : q = n
    · -- q = n: the outerLoop does nothing because len is too large
      cases hqn
      have hn64 : n < 64 := n_lt_64_of_pow2_nat m n hm_eq (hm_eq.symm ▸ h_dvd)
      have hn1_64 : n + 1 < 64 := by
        have := len.toNat_lt; rw [hlen] at this
        exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp this
      have h_noop := outerLoop_noop_pow2 false roots a len (fuel + 1) n hm_eq
        (Or.inl ⟨n + 1, hlen, Nat.lt_succ_of_le le_rfl, hn1_64⟩)
      rw [h_noop]
      exact inv_at_n_implies_ref_ntt n hm_eq v a hinv k
    · -- q < n: the loop has more work to do
      have hq_lt : q < n := lt_of_le_of_ne hq hqn
      have hq2 : q + 2 ≤ n := by
        obtain ⟨d, hd⟩ := hq_even; omega
      have hn64 : n < 64 := n_lt_64_of_pow2_nat m n hm_eq (hm_eq.symm ▸ h_dvd)
      have hgt_neg : ¬(len.toNat * 2 > m) :=
        outerLoop_len_not_gt_nat n q hm_eq hq2 len hlen
      simp only [nttInplace.outerLoop, hgt_neg, ↓reduceIte]
      have hinv' :=
        radix4Middle_advances_inv n q hq2 hm_eq v roots hroots hroots_bnd h_dvd a hinv len hlen
      -- Two sub-cases: q + 2 = n (last iteration) or q + 2 < n (more iterations)
      by_cases hq2n : q + 2 = n
      · -- Last iteration: after radix4Middle, invariant is at level n
        -- The invariant is now at level n. The loop should do nothing from here.
        have hinv_n : outerLoop_inv n n (le_refl n) hm_eq v
            (radix4Middle false roots (len >>> 1).toNat len.toNat (m / (2 * len.toNat)) 0 a) := by
          convert hinv' using 1; omega
        have h_noop := outerLoop_noop_pow2 false roots
          (radix4Middle false roots (len >>> 1).toNat len.toNat (m / (2 * len.toNat)) 0 a)
          (len <<< 2) fuel n hm_eq
        -- Need to show (len <<< 2) is either 0 or a large power of 2
        by_cases hq3_strict : q + 3 < 64
        · -- No overflow
          have hlen' := outerLoop_len_shift q len hlen (by omega)
          have h1 : (len <<< 2).toNat = 2 ^ (q + 3) := hlen'
          have h2 := h_noop (Or.inl ⟨q + 3, h1, by omega, hq3_strict⟩)
          simp only [h2]
          exact inv_at_n_implies_ref_ntt n hm_eq v _ hinv_n k
        · -- q + 3 ≥ 64, shift overflows to 0
          -- len.toNat = 2^(q+1) with q + 3 ≥ 64, so q ≥ 61 and q+2 = n
          have hlen_shift_zero : (len <<< 2).toNat = 0 := by
            simp only [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat, hlen, Nat.shiftLeft_eq]
            norm_num
            have hq_ge : q ≥ 61 := by omega
            have hq_le : q ≤ 62 := by omega -- since q + 2 = n < 64
            interval_cases q <;> norm_num
          have h2 := h_noop (Or.inr hlen_shift_zero)
          simp only [h2]
          exact inv_at_n_implies_ref_ntt n hm_eq v _ hinv_n k
      · -- More iterations remaining
        have hq2_lt : q + 2 < n := by omega
        have hlen' : (len <<< 2).toNat = 2 ^ (q + 2 + 1) :=
          outerLoop_len_shift q len hlen (by omega)
        have heven' : Even (n - (q + 2)) := by
          obtain ⟨d, hd⟩ := hq_even; exact ⟨d - 1, by omega⟩
        exact ih (q + 2)
          (radix4Middle false roots (len >>> 1).toNat len.toNat (m / (2 * len.toNat)) 0 a)
          hq2 hinv' (len <<< 2) hlen' heven' (by omega)


/-- When `nBlocks = 0` for the given `len` (and this is maintained under doubling),
    the outerLoop is the identity. -/
lemma outerLoop_stable_at_n {m : ℕ} (n : ℕ) (hm_eq : m = 2 ^ n)
    (roots a : Vector UInt32 m) (len : UInt64) (fuel : ℕ)
    (h_inv : len.toNat = 0 ∨ ∃ j, n ≤ j ∧ j < 64 ∧ len.toNat = 2 ^ j) :
    nttInplace.outerLoop false roots a len fuel = a := by
  induction fuel generalizing len with
  | zero => simp only [nttInplace.outerLoop]
  | succ f ih =>
    simp only [nttInplace.outerLoop]
    by_cases hgt : len.toNat * 2 > m
    · simp only [if_pos hgt]
    · simp only [hgt, ↓reduceIte]
      have h_nBlocks : m / (2 * len.toNat) = 0 := by
        rcases h_inv with h0 | ⟨j, hj_ge, _, hlenj⟩
        · simp only [h0, mul_zero, Nat.div_zero]
        · rw [hm_eq, hlenj, (by ring : 2 * 2 ^ j = 2 ^ (j + 1))]
          exact Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
      rw [h_nBlocks]
      change nttInplace.outerLoop false roots a (len <<< 2) f = a
      apply ih
      have hshift : (len <<< 2).toNat = len.toNat * 4 % 2 ^ 64 := by
        simp only [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq,
                   show (2 : UInt64).toNat = 2 from rfl, show 2 % 64 = 2 from by norm_num]
      have h_inv' :
          (len <<< 2).toNat = 0 ∨ ∃ j, n ≤ j ∧ j < 64 ∧ (len <<< 2).toNat = 2 ^ j := by
        rw [hshift]
        rcases h_inv with h0 | ⟨j, hj_ge, hj_lt, hlenj⟩
        · left; simp only [h0, zero_mul, Nat.zero_mod]
        · rw [hlenj, (by ring : 2 ^ j * 4 = 2 ^ (j + 2))]
          by_cases hjb : j + 2 < 64
          · right; exact ⟨j + 2, by omega, hjb,
              Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hjb)⟩
          · left; exact Nat.dvd_iff_mod_eq_zero.mp (Nat.pow_dvd_pow 2 (by omega))
      exact h_inv'
