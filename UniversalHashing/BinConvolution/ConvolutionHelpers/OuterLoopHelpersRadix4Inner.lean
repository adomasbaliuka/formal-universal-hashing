/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib
import UniversalHashing.BinConvolution.ConvolutionHelpers.DFTLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.SolutionHelpers
import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpers



/-!
# Single-block radix-4 correctness

This file contains `radix4Inner_single_block_correct`, split out from `OuterLoopHelpers`
to keep per-file elaboration memory bounded.
-/

set_option maxHeartbeats 8000000 in
-- The proof elaborates very slowly due to the large number of local hypotheses and rewrites.
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
    simp [UInt64.toNat_shiftRight, hlen, Nat.shiftRight_eq_div_pow, Nat.pow_succ']
  set s : UInt64 := len >>> 1 with hs_def
  have hlen_butterfly : len.toNat = 2 * s.toNat := by rw [hs_eq, hlen]; ring
  have hdvd : 2 * len.toNat ∣ m := by
    rw [hm_eq, hlen, show 2 * 2 ^ (q + 1) = 2 ^ (q + 2) from by ring]
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
    rw [h_i2_len_j2_toNat]
    have : (2 : ℕ) ^ (q + 1) = 2 * 2 ^ q := by ring
    rw [this]; ring
  have hpos3_match : (i2 + len + j2u + s).toNat = (4 * b + 3) * 2 ^ q + j2nat := by
    rw [h_i2_len_j2_s_toNat]
    have h1 : (2 : ℕ) ^ (q + 1) = 2 * 2 ^ q := by ring
    rw [h1]; ring
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
    rw [show (0 : ℕ) + j2nat = j2nat from by omega]
    -- Now split (1 + rest) = 1 + (s.toNat-j2nat-1), starting at j2nat
    rw [radix4Inner_comp]
    -- Second split: radix4Inner ... (s.toNat-j2nat-1) (j2nat+1) (... 1 j2nat (... j2nat 0 a))
    -- And radix4Inner ... 1 j2nat A = butterfly4 A false roots s.toNat len.toNat i2.toNat j2u.toNat
    have h_inner1 :
        radix4Inner false roots s.toNat len.toNat i2.toNat 1 j2nat
            (radix4Inner false roots s.toNat len.toNat i2.toNat j2nat 0 a) =
        butterfly4 (radix4Inner false roots s.toNat len.toNat i2.toNat j2nat 0 a)
            false roots s.toNat len.toNat i2.toNat j2u.toNat := by
      simp [radix4Inner, hj2u_toNat]
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
      (i2 + len + j2.toUInt64 + s).toNat ≠ posval := by
    intro j2 hj2 hj2_ne posval hpos
    rw [h_pos0_gen j2 hj2, h_pos1_gen j2 hj2, h_pos2_gen j2 hj2, h_pos3_gen j2 hj2]
    have hpow_e : 2 ^ (q + 2) = 2 ^ q + 2 ^ q + 2 ^ q + 2 ^ q := by ring
    have hpow1 : 2 ^ (q + 1) = 2 ^ q + 2 ^ q := by ring
    rcases hpos with h | h | h | h <;> subst h <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
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
      exact ⟨by omega, by omega, by omega, by omega⟩
    · intro j2 hlo hhi
      obtain ⟨hn0, hn1, hn2, hn3⟩ :=
        h_ne_gen j2 (hlt_range j2 hlo hhi) (hne j2 hlo hhi) posval hpos
      rw [h_pos0_gen j2 (hlt_range j2 hlo hhi), ← hi2_toNat] at hn0
      rw [h_pos1_gen j2 (hlt_range j2 hlo hhi), ← hi2_toNat, ← hs_eq] at hn1
      rw [h_pos2_gen j2 (hlt_range j2 hlo hhi), ← hi2_toNat] at hn2
      rw [h_pos3_gen j2 (hlt_range j2 hlo hhi), ← hi2_toNat, ← hs_eq] at hn3
      exact ⟨by omega, by omega, by omega, by omega⟩
  have h_leading_pos0 := h_ne_at a j2nat 0 _ hbnd0 (by rw [h_i2_j2_toNat]; left; rfl)
      (fun _ _ hhi => by omega) (fun _ _ hhi => by omega)
  have h_leading_pos1 := h_ne_at a j2nat 0 _ hbnd1 (by rw [h_i2_j2_s_toNat]; right; left; rfl)
      (fun _ _ hhi => by omega) (fun _ _ hhi => by omega)
  have h_leading_pos2 :=
    h_ne_at a j2nat 0 _ hbnd2 (by rw [h_i2_len_j2_toNat]; right; right; left; rfl)
      (fun _ _ hhi => by omega) (fun _ _ hhi => by omega)
  have h_leading_pos3 :=
    h_ne_at a j2nat 0 _ hbnd3 (by rw [h_i2_len_j2_s_toNat]; right; right; right; rfl)
      (fun _ _ hhi => by omega) (fun _ _ hhi => by omega)
  have h_trailing_pos0 : ∀ B,
      (radix4Inner false roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
          (j2nat + 1) B)[(i2 + j2u).toNat]'hbnd0 = B[(i2 + j2u).toNat]'hbnd0 :=
    fun B => h_ne_at B _ _ _ hbnd0 (by rw [h_i2_j2_toNat]; left; rfl)
      (fun _ _ hhi => by rw [← hs_eq]; omega)
      (fun _ hlo _ => by omega)
  have h_trailing_pos1 : ∀ B,
      (radix4Inner false roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
          (j2nat + 1) B)[(i2 + j2u + s).toNat]'hbnd1 = B[(i2 + j2u + s).toNat]'hbnd1 :=
    fun B => h_ne_at B _ _ _ hbnd1 (by rw [h_i2_j2_s_toNat]; right; left; rfl)
      (fun _ _ hhi => by rw [← hs_eq]; omega)
      (fun _ hlo _ => by omega)
  have h_trailing_pos2 : ∀ B,
      (radix4Inner false roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
          (j2nat + 1) B)[(i2 + len + j2u).toNat]'hbnd2 = B[(i2 + len + j2u).toNat]'hbnd2 :=
    fun B => h_ne_at B _ _ _ hbnd2 (by rw [h_i2_len_j2_toNat]; right; right; left; rfl)
      (fun _ _ hhi => by rw [← hs_eq]; omega)
      (fun _ hlo _ => by omega)
  have h_trailing_pos3 : ∀ B,
      (radix4Inner false roots s.toNat len.toNat i2.toNat (s.toNat - j2nat - 1)
          (j2nat + 1) B)[(i2 + len + j2u + s).toNat]'hbnd3 = B[(i2 + len + j2u + s).toNat]'hbnd3 :=
    fun B => h_ne_at B _ _ _ hbnd3 (by rw [h_i2_len_j2_s_toNat]; right; right; right; rfl)
      (fun _ _ hhi => by rw [← hs_eq]; omega)
      (fun _ hlo _ => by omega)
  -- Apply butterfly4_forward_ZMod_combined to the leading vector.
  set A_lead := radix4Inner false roots s.toNat len.toNat i2.toNat j2nat 0 a with hA_lead_def
  have hA_lead_bnd : A_lead.all (· < mod32) := by
    rw [hA_lead_def]
    exact radix4Inner_bound false roots s.toNat len.toNat i2.toNat j2nat 0 a ha_bnd
  -- Convert UInt64-phrased bounds to ℕ-arithmetic form for butterfly4_forward_ZMod_combined
  have hbnd0' : i2.toNat + j2u.toNat < m := by
    rw [hi2_toNat, hj2u_toNat]; rw [h_i2_j2_toNat] at hbnd0; exact hbnd0
  have hbnd1' : i2.toNat + j2u.toNat + s.toNat < m := by
    rw [hi2_toNat, hj2u_toNat, hs_eq]; rw [h_i2_j2_s_toNat] at hbnd1; exact hbnd1
  have hbnd2' : i2.toNat + len.toNat + j2u.toNat < m := by
    rw [hi2_toNat, hj2u_toNat]; rw [h_i2_len_j2_toNat] at hbnd2; linarith
  have hbnd3' : i2.toNat + len.toNat + j2u.toNat + s.toNat < m := by
    rw [hi2_toNat, hj2u_toNat, hs_eq]; rw [h_i2_len_j2_s_toNat] at hbnd3; linarith
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
    rw [show 4 * 2 ^ q * K = 2 ^ q * (4 * K) from by ring,
        Nat.mul_div_cancel_left _ hpos_q]
  have h_omega_q : ω_top ^ 4 = ωq := by
    rw [hωq_def, hω_top_def, ← pow_mul]
    congr 1
    rw [show (mod64.toNat - 1) / 2 ^ (q + 2) * 4 = 4 * ((mod64.toNat - 1) / 2 ^ (q + 2))
        from by ring, h_div_4]
  -- Express τ₁, τ₂, τ₃ in terms of ω_top
  have h_tau2 : (primRoot.toNat : ZMod mod32.toNat) ^
      ((mod64.toNat - 1) / (2 * len.toNat) * j2u.toNat) = ω_top ^ j2nat := by
    rw [hω_top_def, ← pow_mul, hj2u_toNat]
    congr 1
    rw [hlen, show 2 * 2 ^ (q + 1) = 2 ^ (q + 2) from by ring]
  have h_tau3 : (primRoot.toNat : ZMod mod32.toNat) ^
      ((mod64.toNat - 1) / (2 * len.toNat) * (s.toNat + j2u.toNat)) = ω_top ^ (2 ^ q + j2nat) := by
    rw [hω_top_def, ← pow_mul, hj2u_toNat, hs_eq]
    congr 1
    rw [hlen, show 2 * 2 ^ (q + 1) = 2 ^ (q + 2) from by ring]
  have h_tau1 : (primRoot.toNat : ZMod mod32.toNat) ^
      ((mod64.toNat - 1) / len.toNat * j2u.toNat) = (ω_top ^ 2) ^ j2nat := by
    rw [← pow_mul, hω_top_def, ← pow_mul, hj2u_toNat]
    congr 1
    obtain ⟨K, hK⟩ := h_dvd_q2
    have hpos : (2 : ℕ) ^ (q + 2) > 0 := Nat.two_pow_pos _
    have hpos1 : (2 : ℕ) ^ (q + 1) > 0 := Nat.two_pow_pos _
    have h_eq : (2 : ℕ) ^ (q + 2) = 2 * 2 ^ (q + 1) := by ring
    rw [hlen, hK, Nat.mul_div_cancel_left _ hpos, h_eq]
    rw [show 2 * 2 ^ (q + 1) * K = 2 ^ (q + 1) * (2 * K) from by ring,
        Nat.mul_div_cancel_left _ hpos1]
    ring
  -- Compute A₀ via h_inv_k and ntt_sub_input_block_0
  have hb_pow' : b < 2 ^ (n - q - 2) := hb_pow
  have h_idx_in_bnd : ∀ k, k < 4 → (4 * b + k) * 2 ^ q + j2nat < m := by
    intro k hk
    rw [hm_eq]
    have hbexpand : (b + 1) * 2 ^ (q + 2) = b * 2 ^ (q + 2) + 2 ^ (q + 2) := by ring
    have hpow_e : 2 ^ (q + 2) = 4 * 2 ^ q := by ring
    have h_decomp : (4 * b + k) * 2 ^ q + j2nat = b * 2 ^ (q + 2) + (k * 2 ^ q + j2nat) := by
      rw [Nat.add_mul, hpow_e]; ring
    rw [h_decomp]
    have hpow : k * 2 ^ q + j2nat < 2 ^ (q + 2) := by
      rw [hpow_e]
      have : k * 2 ^ q ≤ 3 * 2 ^ q := Nat.mul_le_mul_right _ (by omega)
      omega
    omega
  -- A-values from h_inv_k
  have hA0_eq : ((A_lead[(i2 + j2u).toNat]'hbnd0).toNat : ZMod mod32.toNat) =
      ref_ntt q ωq (ntt_sub_input n q (by omega) hm_eq v (4 * b + 0)) ⟨j2nat, hj2_lt⟩ := by
    rw [h_leading_pos0]
    have h := h_inv_k 0 (by decide) ⟨j2nat, hj2_lt⟩ (h_idx_in_bnd 0 (by decide))
    have heq : a[(i2 + j2u).toNat]'hbnd0 =
        a[(4 * b + 0) * 2 ^ q + j2nat]'(h_idx_in_bnd 0 (by decide)) :=
      getElem_congr_idx hpos0_match
    rw [heq]; exact h
  have hA1_eq : ((A_lead[(i2 + j2u + s).toNat]'hbnd1).toNat : ZMod mod32.toNat) =
      ref_ntt q ωq (ntt_sub_input n q (by omega) hm_eq v (4 * b + 1)) ⟨j2nat, hj2_lt⟩ := by
    rw [h_leading_pos1]
    have h := h_inv_k 1 (by decide) ⟨j2nat, hj2_lt⟩ (h_idx_in_bnd 1 (by decide))
    have heq : a[(i2 + j2u + s).toNat]'hbnd1 =
        a[(4 * b + 1) * 2 ^ q + j2nat]'(h_idx_in_bnd 1 (by decide)) :=
      getElem_congr_idx hpos1_match
    rw [heq]; exact h
  have hA2_eq : ((A_lead[(i2 + len + j2u).toNat]'hbnd2).toNat : ZMod mod32.toNat) =
      ref_ntt q ωq (ntt_sub_input n q (by omega) hm_eq v (4 * b + 2)) ⟨j2nat, hj2_lt⟩ := by
    rw [h_leading_pos2]
    have h := h_inv_k 2 (by decide) ⟨j2nat, hj2_lt⟩ (h_idx_in_bnd 2 (by decide))
    have heq : a[(i2 + len + j2u).toNat]'hbnd2 =
        a[(4 * b + 2) * 2 ^ q + j2nat]'(h_idx_in_bnd 2 (by decide)) :=
      getElem_congr_idx hpos2_match
    rw [heq]; exact h
  have hA3_eq : ((A_lead[(i2 + len + j2u + s).toNat]'hbnd3).toNat : ZMod mod32.toNat) =
      ref_ntt q ωq (ntt_sub_input n q (by omega) hm_eq v (4 * b + 3)) ⟨j2nat, hj2_lt⟩ := by
    rw [h_leading_pos3]
    have h := h_inv_k 3 (by decide) ⟨j2nat, hj2_lt⟩ (h_idx_in_bnd 3 (by decide))
    have heq : a[(i2 + len + j2u + s).toNat]'hbnd3 =
        a[(4 * b + 3) * 2 ^ q + j2nat]'(h_idx_in_bnd 3 (by decide)) :=
      getElem_congr_idx hpos3_match
    rw [heq]; exact h
  -- Use ntt_sub_input_block_K to rewrite the ntt_sub_input expressions in terms of v at b
  -- Define the f function for ref_ntt at level q+2:
  set f_ntt : Fin (2 ^ (q + 2)) → ZMod mod32.toNat :=
    ntt_sub_input n (q + 2) hq2 hm_eq v b with hf_ntt_def
  have h_sub0_fun : ntt_sub_input n q (by omega) hm_eq v (4 * b + 0) =
      fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val, fin_4mul_lt q j⟩ := by
    funext j
    rw [hf_ntt_def]
    simpa using ntt_sub_input_block_0 n q hq2 hm_eq v b hb_pow' j
  have h_sub1_fun : ntt_sub_input n q (by omega) hm_eq v (4 * b + 1) =
      fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 2, fin_4mul2_lt q j⟩ := by
    funext j
    rw [hf_ntt_def]
    simpa using ntt_sub_input_block_1 n q hq2 hm_eq v b j
  have h_sub2_fun : ntt_sub_input n q (by omega) hm_eq v (4 * b + 2) =
      fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 1, fin_4mul1_lt q j⟩ := by
    funext j
    rw [hf_ntt_def]
    simpa using ntt_sub_input_block_2 n q hq2 hm_eq v b j
  have h_sub3_fun : ntt_sub_input n q (by omega) hm_eq v (4 * b + 3) =
      fun j : Fin (2 ^ q) => f_ntt ⟨4 * j.val + 3, fin_4mul3_lt q j⟩ := by
    funext j
    rw [hf_ntt_def]
    simpa using ntt_sub_input_block_3 n q hq2 hm_eq v b hb_pow' j
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
  -- Bridge UInt64-arithmetic indices to ℕ-arithmetic indices for hbf0..3
  have hpos_eq0 : (i2 + j2u).toNat = i2.toNat + j2u.toNat := by
    rw [h_i2_j2_toNat, hi2_toNat, hj2u_toNat]
  have hpos_eq1 : (i2 + j2u + s).toNat = i2.toNat + j2u.toNat + s.toNat := by
    rw [h_i2_j2_s_toNat, hi2_toNat, hj2u_toNat, hs_eq]
  have hpos_eq2 : (i2 + len + j2u).toNat = i2.toNat + len.toNat + j2u.toNat := by
    rw [h_i2_len_j2_toNat, hi2_toNat, hj2u_toNat]; omega
  have hpos_eq3 : (i2 + len + j2u + s).toNat = i2.toNat + len.toNat + j2u.toNat + s.toNat := by
    rw [h_i2_len_j2_s_toNat, hi2_toNat, hj2u_toNat, hs_eq]; omega
  -- Additional equalities for compound index forms that appear in hbfK RHS
  have hpos_eq01 : (i2 + j2u).toNat + s.toNat = (i2 + j2u + s).toNat := by
    rw [hpos_eq0, hpos_eq1]
  have hpos_eq21 : (i2 + len + j2u).toNat + s.toNat = (i2 + len + j2u + s).toNat := by
    rw [hpos_eq2, hpos_eq3]
  -- Convert hbfK indices from ℕ-arithmetic back to UInt64-form
  simp only [hpos_eq01, hpos_eq21, ← hpos_eq0, ← hpos_eq2] at hbf0 hbf1 hbf2 hbf3
  -- Now case-split on quad
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
    rw [hsplit_idx, hbf0]
    rw [hA0_final, hA1_final, hA2_final, hA3_final]
    rw [h_tau1, h_tau2]
    have hr_eq : r = ⟨j2nat, pow2q_lt_q2 q j2nat hj2_lt⟩ := by
      apply Fin.ext; simp; omega
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
    rw [hsplit_idx, hbf1]
    rw [hA0_final, hA1_final, hA2_final, hA3_final]
    rw [h_tau1, h_tau3]
    have hr_eq : r = ⟨j2nat + 2 ^ q, pow2q_add_q_lt_q2 q j2nat hj2_lt⟩ := by
      apply Fin.ext; simp; omega
    rw [hr_eq, ref_ntt_radix4_q1 q ω_top _ j2nat hj2_lt]
    ring
  · -- quad = 2: idx-position is (i2 + len + j2u).toNat
    have hidx_eq : b * 2 ^ (q + 2) + r.val = (i2 + len + j2u).toNat := by
      rw [h_i2_len_j2_toNat, hr_decomp]
      have : (2 : ℕ) ^ (q + 1) = 2 * 2 ^ q := by ring
      rw [this]; ring
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
    rw [hsplit_idx, hbf2]
    rw [hA0_final, hA1_final, hA2_final, hA3_final]
    rw [h_tau1, h_tau2]
    have hr_eq : r = ⟨j2nat + 2 ^ (q + 1), pow2q_add_q1_lt_q2 q j2nat hj2_lt⟩ := by
      apply Fin.ext
      have h1 : (2 : ℕ) ^ (q + 1) = 2 * 2 ^ q := by ring
      linarith [hr_decomp]
    rw [hr_eq, ref_ntt_radix4_q2]
  · -- quad = 3: idx-position is (i2 + len + j2u + s).toNat
    have hidx_eq : b * 2 ^ (q + 2) + r.val = (i2 + len + j2u + s).toNat := by
      rw [h_i2_len_j2_s_toNat, hr_decomp]
      have : (2 : ℕ) ^ (q + 1) = 2 * 2 ^ q := by ring
      rw [this]; ring
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
    rw [hsplit_idx, hbf3]
    rw [hA0_final, hA1_final, hA2_final, hA3_final]
    rw [h_tau1, h_tau3]
    have hr_eq : r = ⟨j2nat + 2 ^ q + 2 ^ (q + 1), pow2q_add_q_q1_lt_q2 q j2nat hj2_lt⟩ := by
      apply Fin.ext
      have h1 : (2 : ℕ) ^ (q + 1) = 2 * 2 ^ q := by ring
      linarith [hr_decomp]
    rw [hr_eq, ref_ntt_radix4_q3 q ω_top _ j2nat hj2_lt]
    ring
