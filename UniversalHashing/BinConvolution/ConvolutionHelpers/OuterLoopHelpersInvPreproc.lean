/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import UniversalHashing.BinConvolution.ConvolutionHelpers.DFTLemmas
public import UniversalHashing.BinConvolution.ConvolutionHelpers.NttBoundLemmas
public import UniversalHashing.BinConvolution.ConvolutionHelpers.Radix4ForwardLemmas
public import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpers
public import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpersInverseNTT
public import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpersInvFull
public import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpersPreproc




/-!
# Inverse NTT preprocessing invariant

`preprocessing_establishes_inv_inverse`: after `bitRevLoop` (and optional `radix2Pass`),
the `outerLoop_inv_inverse` holds at the starting level `start_q`.

This mirrors `preprocessing_establishes_inv` but for the inverse path:
no `toMont` is applied, and the invariant uses `ntt_sub_input_inv`.
-/

@[expose] public section

lemma preprocessing_establishes_inv_inverse {m : ℕ} (n : ℕ)
    (hm_eq : m = 2 ^ n)
    (h_dvd : m ∣ mod64.toNat - 1)
    (v : Vector UInt32 m) (hv_bound : v.all (· < mod32)) :
    let a1 := bitRevLoop (m - 1) 0 v 0
    let parity := nttInplace.go 64 m 0 &&& 1 != 0
    let a_in := if parity then radix2Pass (m / 2) 0 a1 else a1
    let start_q := if parity then 1 else 0
    ∃ hle : start_q ≤ n,
      outerLoop_inv_inverse n start_q hle hm_eq v a_in := by
  have hn64 : n < 64 := n_lt_64_of_pow2_nat m n hm_eq h_dvd
  set a1 := bitRevLoop (m - 1) 0 v 0 with ha1_def
  -- Bound on a1: bitRevLoop preserves the bound
  have ha1_bound : a1.all (· < mod32) := by
    rw [ha1_def]
    exact bitRevLoop_bound _ _ _ _ hv_bound
  -- a1[p] = v[bitRev n p]  (no toMont)
  have ha1_spec : ∀ (p : ℕ) (hp : p < m),
      a1[p]'hp = v[bitRev n p]'(by rw [hm_eq]; exact bitRev_lt n p) := by
    intro p hp
    rw [ha1_def]
    exact bitRevLoop_spec_m n hm_eq hn64 v p hp (by rw [hm_eq]; exact bitRev_lt n p)
  -- Case split on parity
  by_cases hpar : nttInplace.go 64 m 0 &&& 1 != 0
  · -- Odd case: n is odd, start_q = 1
    have hn_odd : Odd n := by
      by_contra h
      rw [Nat.not_odd_iff_even] at h
      have := go_parity_even_nat m n hm_eq hn64 h
      simp_all
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => by
      subst h; rcases hn_odd with ⟨k, hk⟩; omega)
    have hpar_val_b : (nttInplace.go 64 m 0 &&& 1 != 0) = true := hpar
    change ∃ hle, outerLoop_inv_inverse n
      (if (nttInplace.go 64 m 0 &&& 1 != 0) = true then 1 else 0) hle hm_eq v
      (if (nttInplace.go 64 m 0 &&& 1 != 0) = true then radix2Pass (m / 2) 0 a1 else a1)
    rw [if_pos hpar_val_b, if_pos hpar_val_b]
    refine ⟨hn1, ?_, ?_⟩
    · -- Bound
      exact radix2Pass_bound _ _ _ ha1_bound
    · -- Value correctness for q = 1
      intro b r hb idx hidx
      have hr : r.val = 0 ∨ r.val = 1 := by have := r.isLt; omega
      have h_pow_eq : 2 * 2 ^ (n - 1) = 2 ^ n := by
        rw [(by ring : (2 : ℕ) * 2 ^ (n - 1) = 2 ^ (n - 1 + 1))]
        congr 1; omega
      have h2b1_lt : 2 * b + 1 < m := by
        rw [hm_eq]; have hb' : b < 2 ^ (n - 1) := hb; omega
      have h2b_lt : 2 * b < m := by omega
      have hbRb_lt : bitRev (n - 1) b < 2 ^ (n - 1) := bitRev_lt (n - 1) b
      have hbRb_idx_lt : bitRev (n - 1) b < m := by
        rw [hm_eq]; have : 2 ^ (n - 1) ≤ 2 ^ n :=
          Nat.pow_le_pow_right (by norm_num) (by omega); omega
      have hbRb1_idx_lt : 2 ^ (n - 1) + bitRev (n - 1) b < m := by
        rw [hm_eq]; omega
      have hbR_2b : bitRev n (2 * b) = bitRev (n - 1) b := by
        conv_lhs => rw [(by omega : n = (n - 1) + 1)]
        simp only [bitRev_succ]
        have hmod : (2 * b) % 2 = 0 := by omega
        have hdiv : (2 * b) / 2 = b := by omega
        rw [hmod, hdiv]; ring
      have hbR_2b1 : bitRev n (2 * b + 1) = 2 ^ (n - 1) + bitRev (n - 1) b := by
        conv_lhs => rw [(by omega : n = (n - 1) + 1)]
        simp only [bitRev_succ]
        have hmod : (2 * b + 1) % 2 = 1 := by omega
        have hdiv : (2 * b + 1) / 2 = b := by omega
        rw [hmod, hdiv]; ring
      -- a1[2b] = v[bitRev (n-1) b]  and  a1[2b+1] = v[2^(n-1) + bitRev (n-1) b]
      have ha1_2b : (a1[2 * b]'h2b_lt) = v[bitRev (n - 1) b]'hbRb_idx_lt := by
        have h := ha1_spec (2 * b) h2b_lt
        calc a1[2 * b]'h2b_lt = v[bitRev n (2 * b)]'_ := h
          _ = v[bitRev (n - 1) b]'hbRb_idx_lt := getElem_congr_idx hbR_2b
      have ha1_2b1 : (a1[2 * b + 1]'h2b1_lt) = v[2 ^ (n - 1) + bitRev (n - 1) b]'hbRb1_idx_lt := by
        have h := ha1_spec (2 * b + 1) h2b1_lt
        calc a1[2 * b + 1]'h2b1_lt = v[bitRev n (2 * b + 1)]'_ := h
          _ = v[2 ^ (n - 1) + bitRev (n - 1) b]'hbRb1_idx_lt := getElem_congr_idx hbR_2b1
      -- ntt_sub_input_inv n 1 hn1 hm_eq v b ⟨0, _⟩ = v[bitRev (n-1) b]
      have h_input_0 : (ntt_sub_input_inv n 1 hn1 hm_eq v b) ⟨0, by norm_num⟩ =
          ((v[bitRev (n - 1) b]'hbRb_idx_lt).toNat : ZMod mod32.toNat) := by
        unfold ntt_sub_input_inv
        simp only [Fin.cast]
        congr 2
        change v[(2 ^ (n - 1) * 0 + bitRev (n - 1) b)]'_ = v[bitRev (n - 1) b]'hbRb_idx_lt
        exact getElem_congr_idx (by ring : 2 ^ (n - 1) * 0 + bitRev (n - 1) b = bitRev (n - 1) b)
      have h_input_1 : (ntt_sub_input_inv n 1 hn1 hm_eq v b) ⟨1, by norm_num⟩ =
          ((v[2 ^ (n - 1) + bitRev (n - 1) b]'hbRb1_idx_lt).toNat : ZMod mod32.toNat) := by
        unfold ntt_sub_input_inv
        simp only [Fin.cast]
        congr 2
        change v[(2 ^ (n - 1) * 1 + bitRev (n - 1) b)]'_ =
          v[2 ^ (n - 1) + bitRev (n - 1) b]'hbRb1_idx_lt
        exact getElem_congr_idx
          (by ring : 2 ^ (n - 1) * 1 + bitRev (n - 1) b = 2 ^ (n - 1) + bitRev (n - 1) b)
      -- ref_ntt 1 ω_inv simplifies: ω_inv at exponents 0 is always 1
      rcases hr with hr0 | hr1
      · -- r.val = 0
        have hrr : r = ⟨0, by norm_num⟩ := Fin.ext hr0
        have h_ref : ref_ntt 1
            (((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ 1))⁻¹)
            (ntt_sub_input_inv n 1 hn1 hm_eq v b) r =
            (ntt_sub_input_inv n 1 hn1 hm_eq v b) ⟨0, by norm_num⟩ +
            (ntt_sub_input_inv n 1 hn1 hm_eq v b) ⟨1, by norm_num⟩ := by
          rw [hrr]; simp only [ref_ntt]; simp
        rw [h_ref, h_input_0, h_input_1]
        rw [← show ((a1[2 * b]'h2b_lt).toNat : ZMod mod32.toNat) =
            ((v[bitRev (n - 1) b]'hbRb_idx_lt).toNat : ZMod mod32.toNat) from
          congr_arg (Nat.cast (R := ZMod mod32.toNat)) (congr_arg UInt32.toNat ha1_2b)]
        rw [← show ((a1[2 * b + 1]'h2b1_lt).toNat : ZMod mod32.toNat) =
            ((v[2 ^ (n - 1) + bitRev (n - 1) b]'hbRb1_idx_lt).toNat : ZMod mod32.toNat) from
          congr_arg (Nat.cast (R := ZMod mod32.toNat)) (congr_arg UInt32.toNat ha1_2b1)]
        have hpair := (radix2Pass_ZMod_pair a1 ha1_bound b h2b1_lt).1
        have hidx_eq : idx = 2 * b := by
          change b * 2 ^ 1 + r.val = 2 * b
          rw [hr0]; ring
        rw [show ((radix2Pass (m / 2) 0 a1)[idx]'hidx).toNat =
            ((radix2Pass (m / 2) 0 a1).get ⟨2 * b, by omega⟩).toNat from by
          congr 1; exact getElem_congr_idx hidx_eq]
        exact hpair
      · -- r.val = 1
        have hrr : r = ⟨1, by norm_num⟩ := Fin.ext hr1
        have h_ref : ref_ntt 1
            (((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ 1))⁻¹)
            (ntt_sub_input_inv n 1 hn1 hm_eq v b) r =
            (ntt_sub_input_inv n 1 hn1 hm_eq v b) ⟨0, by norm_num⟩ -
            (ntt_sub_input_inv n 1 hn1 hm_eq v b) ⟨1, by norm_num⟩ := by
          rw [hrr]; simp only [ref_ntt]; simp
        rw [h_ref, h_input_0, h_input_1]
        rw [← show ((a1[2 * b]'h2b_lt).toNat : ZMod mod32.toNat) =
            ((v[bitRev (n - 1) b]'hbRb_idx_lt).toNat : ZMod mod32.toNat) from
          congr_arg (Nat.cast (R := ZMod mod32.toNat)) (congr_arg UInt32.toNat ha1_2b)]
        rw [← show ((a1[2 * b + 1]'h2b1_lt).toNat : ZMod mod32.toNat) =
            ((v[2 ^ (n - 1) + bitRev (n - 1) b]'hbRb1_idx_lt).toNat : ZMod mod32.toNat) from
          congr_arg (Nat.cast (R := ZMod mod32.toNat)) (congr_arg UInt32.toNat ha1_2b1)]
        have hpair := (radix2Pass_ZMod_pair a1 ha1_bound b h2b1_lt).2
        have hidx_eq : idx = 2 * b + 1 := by
          change b * 2 ^ 1 + r.val = 2 * b + 1
          rw [hr1]; ring
        rw [show ((radix2Pass (m / 2) 0 a1)[idx]'hidx).toNat =
            ((radix2Pass (m / 2) 0 a1).get ⟨2 * b + 1, h2b1_lt⟩).toNat from by
          congr 1; exact getElem_congr_idx hidx_eq]
        exact hpair
  · -- Even case: n is even, start_q = 0
    change ∃ hle, outerLoop_inv_inverse n
      (if (nttInplace.go 64 m 0 &&& 1 != 0) = true then 1 else 0) hle hm_eq v
      (if (nttInplace.go 64 m 0 &&& 1 != 0) = true then radix2Pass (m / 2) 0 a1 else a1)
    rw [if_neg hpar, if_neg hpar]
    refine ⟨Nat.zero_le n, ha1_bound, ?_⟩
    intro b r hb idx hidx
    -- r : Fin 1, r.val = 0
    have hr0 : r.val = 0 := by have := r.isLt; omega
    have hidx_b : idx = b := by
      change b * 2 ^ 0 + r.val = b
      rw [hr0]; ring
    have hbRb_lt : bitRev n b < 2 ^ n := bitRev_lt n b
    have hbRb_idx_lt : bitRev n b < m := by rw [hm_eq]; exact hbRb_lt
    -- ref_ntt 0 ω_inv a r = a r  (0-point DFT is identity)
    have h_ref : ref_ntt 0
        (((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ 0))⁻¹)
        (ntt_sub_input_inv n 0 (Nat.zero_le n) hm_eq v b) r =
        (ntt_sub_input_inv n 0 (Nat.zero_le n) hm_eq v b) r := rfl
    rw [h_ref]
    -- ntt_sub_input_inv n 0 ... v b r = v[bitRev n b]
    have h_input : (ntt_sub_input_inv n 0 (Nat.zero_le n) hm_eq v b) r =
        ((v[bitRev n b]'hbRb_idx_lt).toNat : ZMod mod32.toNat) := by
      unfold ntt_sub_input_inv
      simp only [Fin.cast]
      congr 2
      change v[(2 ^ n * r.val + bitRev n b)]'_ = v[bitRev n b]'hbRb_idx_lt
      exact getElem_congr_idx (by rw [hr0]; ring)
    rw [h_input]
    -- a1[idx] = v[bitRev n b]
    have h_ax := ha1_spec idx hidx
    have h_a1_nat : (a1[idx]'hidx).toNat = (v[bitRev n b]'hbRb_idx_lt).toNat := by
      rw [congrArg UInt32.toNat h_ax]
      congr 1
      have heq : bitRev n idx = bitRev n b := by rw [hidx_b]
      exact getElem_congr_idx (c := v) heq
    exact congrArg (Nat.cast (R := ZMod mod32.toNat)) h_a1_nat

end
