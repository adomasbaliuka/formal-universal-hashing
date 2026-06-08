/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib
import UniversalHashing.BinConvolution.ConvolutionHelpers.DFTLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.SolutionHelpers
import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpers


/-! ## Inverse NTT outer-loop infrastructure

These lemmas mirror the forward outer-loop lemmas (`radix4Inner_single_block_correct`,
`radix4Middle_advances_inv`, `outerLoop_from_inv`, `preprocessing_establishes_inv`) but for the
inverse pass (`inverse = true`).  The key differences:
* The butterfly uses `butterfly4_inverse_ZMod_combined` (negated twiddles
  `ω^{(mod64-1)/len * (len - j2)}` instead of `ω^{(mod64-1)/len * j2}`).
* The loop invariant uses the *inverse* root `(ωq)⁻¹` at each level and the sub-input *without*
  the Montgomery preprocessing (`v[...]` instead of `toMont (v[...])`).
The `ref_ntt_radix4_q*` decomposition lemmas are abstract over the root, so they apply unchanged
with the inverse top-level root `ω_top⁻¹`. -/

/-- Structural fact: `butterfly4` (any `inverse` flag) leaves position `i` unchanged when `i` is
    none of the four modified butterfly positions.  Generalises `butterfly4_getElem_ne`. -/
lemma butterfly4_getElem_ne_gen {N : ℕ} (inverse : Bool) (roots a : Vector UInt32 N)
    (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (i : ℕ) (hi : i < N)
    (hne0 : i2 + j2 ≠ i) (hne1 : i2 + j2 + s ≠ i)
    (hne2 : i2 + len + j2 ≠ i) (hne3 : i2 + len + j2 + s ≠ i) :
    (butterfly4 a inverse roots s len i2 j2)[i]'hi = a[i]'hi := by
  simp only [butterfly4]; split_ifs with h3 h1 <;> simp_all

/-- Generalisation of `radix4Inner_getElem_ne` to any `inverse` flag. -/
lemma radix4Inner_getElem_ne_gen {N : ℕ} (inverse : Bool) (roots a : Vector UInt32 N)
    (s len i2 : ℕ) (k j2_start : ℕ) (hi : ℕ) (hlt : hi < N)
    (hbnd : ∀ j2, j2_start ≤ j2 → j2 < j2_start + k →
      i2 + j2 < N ∧ i2 + j2 + s < N ∧ i2 + len + j2 < N ∧ i2 + len + j2 + s < N)
    (hne : ∀ j2, j2_start ≤ j2 → j2 < j2_start + k →
      i2 + j2 ≠ hi ∧ i2 + j2 + s ≠ hi ∧ i2 + len + j2 ≠ hi ∧ i2 + len + j2 + s ≠ hi) :
    (radix4Inner inverse roots s len i2 k j2_start a)[hi]'hlt = a[hi]'hlt := by
  induction k generalizing j2_start a with
  | zero => rfl
  | succ k ih =>
    have hb := hbnd j2_start (le_refl _) (by omega)
    have hn := hne  j2_start (le_refl _) (by omega)
    calc (radix4Inner inverse roots s len i2 (k + 1) j2_start a)[hi]'hlt
        = (radix4Inner inverse roots s len i2 k (j2_start + 1)
            (butterfly4 a inverse roots s len i2 j2_start))[hi]'hlt := rfl
      _ = (butterfly4 a inverse roots s len i2 j2_start)[hi]'hlt :=
            ih (butterfly4 a inverse roots s len i2 j2_start) (j2_start + 1)
               (fun j2 hlo hhi => hbnd j2 (by omega) (by omega))
               (fun j2 hlo hhi => hne  j2 (by omega) (by omega))
      _ = a[hi]'hlt :=
            butterfly4_getElem_ne_gen inverse roots a s len i2 j2_start
               hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hi hlt hn.1 hn.2.1 hn.2.2.1 hn.2.2.2

/-- Generalisation of `radix4Middle_getElem_ne` to any `inverse` flag. -/
lemma radix4Middle_getElem_ne_gen {N : ℕ} (inverse : Bool) (roots a : Vector UInt32 N)
    (s len : ℕ) (k b_start : ℕ) (hi : ℕ) (hlt : hi < N)
    (hbnd : ∀ b, b_start ≤ b → b < b_start + k → ∀ j2, j2 < s →
      let i2 := b * 2 * len
      i2 + j2 < N ∧ i2 + j2 + s < N ∧ i2 + len + j2 < N ∧ i2 + len + j2 + s < N)
    (hne : ∀ b, b_start ≤ b → b < b_start + k → ∀ j2, j2 < s →
      let i2 := b * 2 * len
      i2 + j2 ≠ hi ∧ i2 + j2 + s ≠ hi ∧ i2 + len + j2 ≠ hi ∧ i2 + len + j2 + s ≠ hi) :
    (radix4Middle inverse roots s len k b_start a)[hi]'hlt = a[hi]'hlt := by
  induction k generalizing b_start a with
  | zero => rfl
  | succ k ih =>
    calc (radix4Middle inverse roots s len (k + 1) b_start a)[hi]'hlt
        = (radix4Middle inverse roots s len k (b_start + 1)
            (radix4Inner inverse roots s len (b_start * 2 * len) s 0 a))[hi]'hlt := rfl
      _ = (radix4Inner inverse roots s len (b_start * 2 * len) s 0 a)[hi]'hlt :=
            ih (radix4Inner inverse roots s len (b_start * 2 * len) s 0 a)
               (b_start + 1)
               (fun b hblo hbhi j2 hj2 => hbnd b (by omega) (by omega) j2 hj2)
               (fun b hblo hbhi j2 hj2 => hne  b (by omega) (by omega) j2 hj2)
      _ = a[hi]'hlt :=
            radix4Inner_getElem_ne_gen inverse roots a s len (b_start * 2 * len) s 0 hi hlt
               (fun j2 _ hj2 => hbnd b_start (le_refl _) (by omega) j2 (by omega))
               (fun j2 _ hj2 => hne  b_start (le_refl _) (by omega) j2 (by omega))

/-- Leading `b` blocks of `radix4Middle` do not modify positions at or after `b * 2 * len`. -/
lemma radix4Middle_leading_getElem_eq {N : ℕ} (inverse : Bool)
    (roots a : Vector UInt32 N) (s len b : ℕ)
    (hlen_s : 2 * s ≤ len)
    (hbnd : ∀ b' < b, (b' + 1) * 2 * len ≤ N)
    (target : ℕ) (htarget : target < N)
    (htarget_ge : b * 2 * len ≤ target) :
    (radix4Middle inverse roots s len b 0 a)[target]'htarget = a[target]'htarget :=
  radix4Middle_getElem_ne_gen inverse roots a s len b 0 target htarget
    (fun b' hb'_lo hb'_hi j2 hj2 => by
      have hb'_lt : b' < b := by omega
      have hbp1 := hbnd b' hb'_lt
      -- Key: j2 + s < len (from j2 < s and 2*s ≤ len)
      have hjs : j2 + s < len := by linarith
      -- Expand the block upper bound
      have h_blen : b' * 2 * len + 2 * len ≤ N := by
        have : (b' + 1) * 2 * len = b' * 2 * len + 2 * len := by ring
        linarith
      simp only
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
    (fun b' hb'_lo hb'_hi j2 hj2 => by
      have hb'_lt : b' < b := by omega
      have hbp1 := hbnd b' hb'_lt
      have hjs : j2 + s < len := by linarith
      -- The block b' ends before the start of block b
      have h_bm : b' * 2 * len + 2 * len ≤ b * 2 * len := by nlinarith
      simp only
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩)

/-- For `idx` in block `b` (i.e. `b * 2 * len ≤ idx < (b+1) * 2 * len`),
    the full `radix4Middle ... nBlocks 0 a` at `idx` equals `radix4Inner` applied to block `b`
    of the leading-processed array `radix4Middle ... b 0 a`. -/
lemma radix4Middle_getElem_at_block {N : ℕ} (inverse : Bool)
    (roots a : Vector UInt32 N) (s len nBlocks b : ℕ)
    (hb : b < nBlocks)
    (hlen_s : 2 * s ≤ len)
    (hbnd : ∀ b' < nBlocks, (b' + 1) * 2 * len ≤ N)
    (idx : ℕ) (hidx : idx < N)
    (hidx_hi : idx < (b + 1) * 2 * len) :
    (radix4Middle inverse roots s len nBlocks 0 a)[idx]'hidx =
    (radix4Inner inverse roots s len (b * 2 * len) s 0
      (radix4Middle inverse roots s len b 0 a))[idx]'hidx := by
  -- Step 1: split nBlocks = b + (nBlocks - b) and expose block b
  have step1 : radix4Middle inverse roots s len nBlocks 0 a =
      radix4Middle inverse roots s len (nBlocks - b) b
        (radix4Middle inverse roots s len b 0 a) := by
    conv_lhs => rw [show nBlocks = b + (nBlocks - b) from by omega, radix4Middle_comp]
    simp only [Nat.zero_add]
  -- Step 2: split (nBlocks - b) = 1 + (nBlocks - b - 1) to isolate single block b
  have step2 : radix4Middle inverse roots s len (nBlocks - b) b
      (radix4Middle inverse roots s len b 0 a) =
      radix4Middle inverse roots s len (nBlocks - b - 1) (b + 1)
        (radix4Middle inverse roots s len 1 b
          (radix4Middle inverse roots s len b 0 a)) := by
    conv_lhs => rw [show nBlocks - b = 1 + (nBlocks - b - 1) from by omega, radix4Middle_comp]
  -- Step 3: radix4Middle ... 1 b x = radix4Inner ... (b*2*len) s 0 x (by definition)
  have step3 : ∀ x : Vector UInt32 N,
      radix4Middle inverse roots s len 1 b x =
      radix4Inner inverse roots s len (b * 2 * len) s 0 x := fun _ => rfl
  -- Step 4: trailing blocks [b+1, nBlocks) don't touch idx < (b+1)*2*len
  set a_mid := radix4Middle inverse roots s len b 0 a
  have hfull : radix4Middle inverse roots s len nBlocks 0 a =
      radix4Middle inverse roots s len (nBlocks - b - 1) (b + 1)
        (radix4Inner inverse roots s len (b * 2 * len) s 0 a_mid) := by
    rw [step1, step2, step3]
  have h_trail : (radix4Middle inverse roots s len (nBlocks - b - 1) (b + 1)
      (radix4Inner inverse roots s len (b * 2 * len) s 0 a_mid))[idx]'hidx =
      (radix4Inner inverse roots s len (b * 2 * len) s 0 a_mid)[idx]'hidx :=
    radix4Middle_getElem_ne_gen inverse roots _ s len _ (b + 1) idx hidx
      (fun b' hb'_lo hb'_hi j2 hj2 => by
        have hb'_lt : b' < nBlocks := by omega
        have hbp1 := hbnd b' hb'_lt
        have hjs : j2 + s < len := by linarith
        have h_blen : b' * 2 * len + 2 * len ≤ N := by
          have : (b' + 1) * 2 * len = b' * 2 * len + 2 * len := by ring
          linarith
        simp only; exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
      (fun b' hb'_lo hb'_hi j2 hj2 => by
        -- b' ≥ b+1, so b'*2*len ≥ (b+1)*2*len > idx
        have h_lo : (b + 1) * 2 * len ≤ b' * 2 * len := by nlinarith
        simp only; exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
  rw [hfull, h_trail]

/-- `primRoot^{mod64-1} = 1` in `ZMod mod32.toNat` (Fermat). -/
lemma prim_root_pow_modm1_eq_one :
    (primRoot.toNat : ZMod mod32.toNat) ^ (mod64.toNat - 1) = 1 := by
  rw [mod32_eq_mod]; exact ZMod.pow_card_sub_one_eq_one (by decide)

/-- Inverse twiddle exponent identity: for `L ∣ mod64-1` and `j ≤ L`,
    `ω^{(mod64-1)/L * (L - j)} = ((ω^{(mod64-1)/L})⁻¹)^j` where `ω = primRoot`. -/
lemma twiddle_inv_exp (L j : ℕ) (hL : L ∣ mod64.toNat - 1) (hj : j ≤ L) (hLpos : 0 < L) :
    (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / L * (L - j)) =
      (((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / L))⁻¹) ^ j := by
  have hroot1 : (primRoot.toNat : ZMod mod32.toNat) ^ (mod64.toNat - 1) = 1 :=
    prim_root_pow_modm1_eq_one
  obtain ⟨K, hK⟩ := hL
  have hdiv : (mod64.toNat - 1) / L = K := by rw [hK]; exact Nat.mul_div_cancel_left _ hLpos
  rw [hdiv]
  set ω := (primRoot.toNat : ZMod mod32.toNat) with hω
  have hKL : ω ^ (L * K) = 1 := by rw [← hK]; exact hroot1
  rw [inv_pow, ← pow_mul]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add]
  have hexp : K * (L - j) + K * j = L * K := by
    have h1 : K * (L - j) + K * j = K * ((L - j) + j) := by ring
    rw [h1, Nat.sub_add_cancel hj]; ring
  rw [hexp, hKL]

/-- Sub-input for the inverse NTT: like `ntt_sub_input` but without the Montgomery `toMont`. -/
noncomputable def ntt_sub_input_inv {m : ℕ} (n q : ℕ) (hq : q ≤ n)
    (hm_eq : m = 2 ^ n)
    (v : Vector UInt32 m) (b : ℕ) : Fin (2 ^ q) → ZMod mod32.toNat :=
  fun j =>
    let idx : Fin (2 ^ n) :=
      ⟨2 ^ (n - q) * j.val + bitRev (n - q) b, bitRev_index_lt n q hq j b⟩
    ((v[Fin.cast hm_eq.symm idx]).toNat : ZMod mod32.toNat)

/-- Inverse loop invariant: like `outerLoop_inv` but with the inverse root `(ωq)⁻¹` and the
    inverse sub-input (no `toMont`). -/
def outerLoop_inv_inverse {m : ℕ} (n q : ℕ) (hq : q ≤ n) (hm_eq : m = 2 ^ n)
    (v : Vector UInt32 m)
    (a : Vector UInt32 m) : Prop :=
  a.all (· < mod32) ∧
  ∀ (b : ℕ) (r : Fin (2 ^ q)),
    b < 2 ^ (n - q) →
    let idx := b * 2 ^ q + r.val
    ∀ hidx : idx < m,
      ((a[idx]'hidx).toNat : ZMod mod32.toNat) =
        ref_ntt q
          (((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ q))⁻¹)
          (ntt_sub_input_inv n q hq hm_eq v b) r


lemma ntt_sub_input_inv_block_0 {m : ℕ} (n q : ℕ) (hq2 : q + 2 ≤ n)
    (hm_eq : m = 2 ^ n) (v : Vector UInt32 m)
    (b : ℕ) (hb : b < 2 ^ (n - q - 2)) (j : Fin (2 ^ q)) :
    ntt_sub_input_inv n q (by omega) hm_eq v (4 * b) j =
    ntt_sub_input_inv n (q + 2) hq2 hm_eq v b ⟨4 * j.val, fin_4mul_lt q j⟩ := by
      unfold ntt_sub_input_inv
      -- Apply the lemma bitRev_four_mul to rewrite the left-hand side.
      have h_bitRev : bitRev (n - q) (4 * b) = bitRev (n - q - 2) b := by
        rcases k : n - q with ( _ | _ | k ) <;> simp_all +decide [Nat.pow_succ', Nat.mul_assoc]
        lia
      -- Since the indices are the same, the elements at those indices are the same.
      have h_index_eq :
          2 ^ (n - q) * j.val + bitRev (n - q) (4 * b) =
          2 ^ (n - (q + 2)) * (4 * j.val) + bitRev (n - (q + 2)) b := by
        rw [h_bitRev, show n - q = n - (q + 2) + 2 by omega]
        ring_nf
        norm_num
      grind +extAll

lemma ntt_sub_input_inv_block_1 {m : ℕ} (n q : ℕ) (hq2 : q + 2 ≤ n)
    (hm_eq : m = 2 ^ n) (v : Vector UInt32 m)
    (b : ℕ) (j : Fin (2 ^ q)) :
    ntt_sub_input_inv n q (by omega) hm_eq v (4 * b + 1) j =
    ntt_sub_input_inv n (q + 2) hq2 hm_eq v b ⟨4 * j.val + 2, fin_4mul2_lt q j⟩ := by
      -- LHS index: `2^(n-q) * j + bitRev(n-q, 4*b + 1)`.
      have h_index_lhs :
          2 ^ (n - q) * j.val + bitRev (n - q) (4 * b + 1) =
          2 ^ (n - (q + 2)) * (4 * j.val + 2) + bitRev (n - (q + 2)) b := by
        rw [show n - q = n - (q + 2) + 2 by omega, bitRev_four_mul_add_one]
        ring
      unfold ntt_sub_input_inv
      grind

lemma ntt_sub_input_inv_block_2 {m : ℕ} (n q : ℕ) (hq2 : q + 2 ≤ n)
    (hm_eq : m = 2 ^ n) (v : Vector UInt32 m)
    (b : ℕ) (j : Fin (2 ^ q)) :
    ntt_sub_input_inv n q (by omega) hm_eq v (4 * b + 2) j =
    ntt_sub_input_inv n (q + 2) hq2 hm_eq v b ⟨4 * j.val + 1, fin_4mul1_lt q j⟩ := by
      unfold ntt_sub_input_inv
      -- The expressions are equal by simplifying exponents.
      have h_exp : n - q = n - (q + 2) + 2 := by omega
      simp +decide [h_exp]
      norm_num [show 4 * b = 2 * (2 * b) by ring, Nat.add_div]
      ring_nf

lemma ntt_sub_input_inv_block_3 {m : ℕ} (n q : ℕ) (hq2 : q + 2 ≤ n)
    (hm_eq : m = 2 ^ n) (v : Vector UInt32 m)
    (b : ℕ) (hb : b < 2 ^ (n - q - 2)) (j : Fin (2 ^ q)) :
    ntt_sub_input_inv n q (by omega) hm_eq v (4 * b + 3) j =
    ntt_sub_input_inv n (q + 2) hq2 hm_eq v b ⟨4 * j.val + 3, fin_4mul3_lt q j⟩ := by
      unfold ntt_sub_input_inv
      have h_bitRev :
          bitRev (n - q) (4 * b + 3) =
          2 ^ (n - q - 1) + 2 ^ (n - q - 2) + bitRev (n - q - 2) b := by
        rcases n' : n - q with ( _ | _ | n' ) <;> simp_all +decide [Nat.pow_succ']
        · omega
        · omega
        · norm_num [Nat.add_mod, Nat.add_div, Nat.mul_mod, Nat.mul_div_assoc, Nat.mul_comm]
          ring
      -- The two indices are equal by simplifying exponents.
      have h_exp :
          2 ^ (n - q) * j.val + 2 ^ (n - q - 1) + 2 ^ (n - q - 2) =
          2 ^ (n - (q + 2)) * (4 * j.val + 3) := by
        rw [show n - q = n - (q + 2) + 2 by omega]
        ring_nf
        norm_num [Nat.add_comm 2, pow_add]
        ring
      grind
