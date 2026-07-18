/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Ineq
public import UniversalHashing.BinConvolution.ConvolutionHelpers.MontgomeryLemmas
public import UniversalHashing.BinConvolution.ConvolutionDefs


/-!
#  ── Root table
-/

@[expose] public section


/-
`rootsInner wm halfLen k 0 v` sets position `halfLen + j` to `montPow v[halfLen] wm j`
for every `j ≤ k` (provided indices are in bounds).
-/
lemma rootsInner_montPow (wm : UInt32) (halfLen : ℕ) {n : ℕ}
    (k j : ℕ) (v : Vector UInt32 n) (hj : j ≤ k) (hn : halfLen + k < n) :
    (rootsInner wm halfLen k 0 v)[halfLen + j]'(by omega) =
      montPow (v[halfLen]'(by omega)) wm j := by
  revert v j
  induction k generalizing halfLen with
  | zero =>
    -- In the base case where `k = 0`, `rootsInner` returns `v` unchanged.
    intros j v hj
    simp only [rootsInner]
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    rfl
  | succ k ih =>
    intro j v hj
    by_cases hj0 : j = 0
    · rw [rootsInner]
      split_ifs <;> simp_all only [zero_add, add_zero]
      · have h_preserve : ∀ (k : ℕ) (i : ℕ) (v : Vector UInt32 n),
              (rootsInner wm halfLen k i v)[halfLen]'(by linarith) =
              v[halfLen]'(by linarith) := by
          intros k i v; exact (by
          induction k generalizing i v with
          | zero => simp_all only [rootsInner]
          | succ k ih =>
            simp_all only [rootsInner]
            split_ifs <;> first | rfl | (rw [Vector.getElem_set_ne]; omega))
        rw [h_preserve]
        rw [Vector.getElem_set] ; aesop
      · linarith
      · linarith
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := Nat.exists_eq_succ_of_ne_zero hj0
      convert ih (halfLen + 1) (by linarith) j'
          (rootsInner wm halfLen 1 0 v) (by linarith) using 1
      · rw [show rootsInner wm halfLen (k + 1) 0 v =
                  rootsInner wm (halfLen + 1) k 0 (rootsInner wm halfLen 1 0 v) from ?_]
        · ac_rfl
        · -- By definition of `rootsInner`, we can split the application into two parts.
          have h_split : ∀ (k : ℕ) (i : ℕ) (v : Vector UInt32 n),
              rootsInner wm halfLen (k + 1) i v =
              rootsInner wm (halfLen + 1) k i (rootsInner wm halfLen 1 i v) := by
            intros k i v
            induction k generalizing i v with
            | zero => simp_all only [rootsInner]
            | succ k ih =>
              simp_all only [rootsInner]
              rw [show halfLen + (i + 1) = halfLen + 1 + i from by omega]
          exact h_split k 0 v
      · rw [show rootsInner wm halfLen 1 0 v =
                  v.set (halfLen + 1) (montMul (v[halfLen]) wm)
                    (by linarith) from ?_]
        · all_goals generalize_proofs at *
          simp only [Vector.getElem_set_self, montPow]
          exact Nat.recOn j' rfl fun n ihn => by
            rw [show montPow (montMul v[halfLen] wm) wm (n + 1) =
                    montMul (montPow (montMul v[halfLen] wm) wm n) wm from rfl,
                 show montPow v[halfLen] wm (n + 1) =
                    montMul (montPow v[halfLen] wm n) wm from rfl, ihn] 
        · all_goals generalize_proofs at *
          simp only [rootsInner, Nat.add_zero]
          aesop

/-
`rootsInner` does not modify positions at index ≤ `halfLen + i`.
-/
lemma rootsInner_preserves_below (wm : UInt32) (halfLen : ℕ) {n : ℕ}
    (k i pos : ℕ) (v : Vector UInt32 n) (hpos : pos < n) (h : pos ≤ halfLen + i) :
    (rootsInner wm halfLen k i v)[pos]'hpos = v[pos]'hpos := by
  induction k generalizing i v with
  | zero => rfl
  | succ k ih =>
    simp only [rootsInner]
    rw [ih (i + 1) _ (by omega)]
    split_ifs <;> first | rfl | (rw [Vector.getElem_set_ne]; omega)

/-
When `wm.toNat = (w * montR1.toNat) % mod64`, the iterated product satisfies
`(montPow montR1 wm j).toNat = (w ^ j * montR1.toNat) % mod64`.
This is the Montgomery-domain geometric series: montR1 = R, and multiplying by
`wm = w·R` (in Montgomery domain) advances the power of `w` by one each step.
-/
lemma montPow_spec (wm : UInt32) (w j : ℕ)
    (hwm : wm.toNat = (w * montR1.toNat) % mod32.toNat) :
    (montPow montR1 wm j).toNat = (w ^ j * montR1.toNat) % mod32.toNat := by
  have h_ind :
      ∀ (j : ℕ), (montPow montR1 wm j).toNat ≡ w ^ j * montR1.toNat [MOD mod32.toNat] := by
    intro j
    have h_ind_step :
        ∀ (j : ℕ), (montPow montR1 wm (j + 1)).toNat =
          montMulNat (montPow montR1 wm j).toNat wm.toNat := by
      intro j
      rw [montPow]
      apply mont_mul_eq_nat
      · induction j with
        | zero => exact (by decide : montR1.toNat < mod32.toNat)
        | succ j ih =>
          exact mont_mul_correct _ _ ih
              (show wm.toNat < mod32.toNat from hwm.symm ▸ Nat.mod_lt _ (by decide))
              |>.1 |> fun h => by simpa [montPow] using h
      · exact hwm.symm ▸ Nat.mod_lt _ (by decide)
    induction j with
    | zero => simp +decide [montPow]
    | succ j ih =>
      have h_ind_step :
          montMulNat (montPow montR1 wm j).toNat wm.toNat * 2 ^ 32 ≡
          (montPow montR1 wm j).toNat * wm.toNat [MOD mod32.toNat] := by
        apply mont_mul_nat_congr
      have h_ind_step :
          montMulNat (montPow montR1 wm j).toNat wm.toNat * 2 ^ 32 ≡
          w ^ (j + 1) * montR1.toNat * 2 ^ 32 [MOD mod32.toNat] := by
        simp_all only [← ZMod.natCast_eq_natCast_iff, mul_assoc, Nat.cast_mul,
                               Nat.cast_pow, Nat.reducePow, ZMod.natCast_mod]
        rw [MONT_R1_ZMod] ; ring
      simp_all only [Nat.modEq_iff_dvd, Nat.cast_mul, Nat.cast_pow, Nat.reducePow]
      have h_ind_step : (mod32.toNat : ℤ) ∣
          (w ^ (j + 1) * montR1.toNat -
            montMulNat (montPow montR1 wm j).toNat (w * montR1.toNat % mod32.toNat)) *
          4294967296 := by
        convert h_ind_step using 1 ; ring
      exact (Int.dvd_of_dvd_mul_left_of_gcd_one h_ind_step <| by decide)
  rw [← h_ind j, Nat.mod_eq_of_lt]
  induction j with
  | zero => exact (by decide : montR1.toNat < mod32.toNat)
  | succ j ih =>
    have := mont_mul_correct (montPow montR1 wm j) wm ih (by
      exact hwm.symm ▸ Nat.mod_lt _ (by decide))
    exact this.1

lemma nat_toUInt64_faithful (m : ℕ) (hm : m < 2 ^ 64) : m.toUInt64.toNat = m := by
  simp only [Nat.toUInt64, UInt64.toNat, UInt64.ofNat, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hm

/-- ℕ-variant: `(2^(s+1)).toUInt64.toNat = 2^(s+1)` when `s < 63`, so `≤ n` in ℕ. -/
lemma pow2_toUInt64_le_nat (s n : ℕ) (hs : s < 63) (h : 2 ^ (s + 1) ≤ n) :
    ¬(((2 ^ (s + 1) : ℕ).toUInt64).toNat > n) := by
  have key : ((2 ^ (s + 1) : ℕ).toUInt64).toNat = 2 ^ (s + 1) :=
    nat_toUInt64_faithful _ (Nat.pow_lt_pow_right (by norm_num) (by omega))
  omega

lemma pow2_toUInt64_halfLen (s : ℕ) (hs : s < 63) :
    ((2 ^ (s + 1) : ℕ).toUInt64 / 2).toNat = 2 ^ s := by
  have hb : (2 ^ (s + 1) : ℕ) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [UInt64.toNat_div, nat_toUInt64_faithful _ hb, show (2 : UInt64).toNat = 2 from rfl, pow_succ]
  exact Nat.mul_div_cancel _ (by norm_num)

lemma pow2_toUInt64_shift (s : ℕ) (_hs : s < 63) :
    ((2 ^ (s + 1) : ℕ).toUInt64 <<< 1) = (2 ^ (s + 2) : ℕ).toUInt64 := by
  rw [← UInt64.toNat_inj]
  simp [UInt64.toNat_shiftLeft, Nat.toUInt64, UInt64.toNat_ofNat, Nat.shiftLeft_eq, pow_succ]

/-
After the target iteration, subsequent iterations of the outer loop
preserve position `2^K + j` because all subsequent halfLens are > 2^K + j.
-/
lemma outer_preserves_target (n : ℕ) (hN : 0 < n)
    (v : Vector UInt32 n) (s f K j : ℕ)
    (hs_gt_K : s > K) (hj : j < 2 ^ K)
    (hKn : 2 ^ K + j < n)
    (hs_lt : s < 64) :
    (ensureRoots.outer n v ((2 ^ (s + 1) : ℕ).toUInt64) hN f)[2 ^ K + j]'hKn =
      v[2 ^ K + j]'hKn := by
  induction f generalizing v s with
  | zero => simp only [ensureRoots.outer]
  | succ f ih =>
    have hpos_ge_one : 1 ≤ 2 ^ K + j := by
      rcases Nat.eq_zero_or_pos K with hK0 | hK1
      · subst hK0; simp at hj; omega
      · have h2K : 2 ≤ 2 ^ K := calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK1
        omega
    by_cases hs63 : s < 63
    · have h_halfLen : ((2 ^ (s + 1) : ℕ).toUInt64 / 2).toNat = 2 ^ s :=
        pow2_toUInt64_halfLen s hs63
      have h_K_lt_s : 2 ^ K + j < 2 ^ s := by
        have h1 : 2 ^ K + j < 2 ^ (K + 1) := by
          have hpow : 2 ^ (K + 1) = 2 ^ K + 2 ^ K := by rw [pow_succ]; ring
          omega
        exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hs_gt_K)
      have h_neq : 2 ^ K + j ≠ ((2 ^ (s + 1) : ℕ).toUInt64 / 2).toNat := by
        rw [h_halfLen]; omega
      have h_le : 2 ^ K + j ≤ ((2 ^ (s + 1) : ℕ).toUInt64 / 2).toNat + 0 := by
        rw [h_halfLen]; omega
      have h_shift : ((2 ^ (s + 1) : ℕ).toUInt64 <<< 1) = (2 ^ (s + 2) : ℕ).toUInt64 :=
        pow2_toUInt64_shift s hs63
      unfold ensureRoots.outer
      split_ifs with h_gt
      · rfl
      · simp only [h_shift, ih _ (s + 1) (by omega) (by omega),
          rootsInner_preserves_below _ _ _ _ _ _ hKn h_le,
          Vector.getElem_set, Ne.symm h_neq, if_false]
    · have hs_eq : s = 63 := by omega
      subst hs_eq
      have h_half_eq : ((2 ^ (63 + 1) : ℕ).toUInt64 / 2).toNat = 0 := by decide
      have h_shift_eq : ((2 ^ (63 + 1) : ℕ).toUInt64 <<< 1) = (2 ^ (63 + 1) : ℕ).toUInt64 := by
        decide
      have h_inner_id : ∀ (wm : UInt32) {N : ℕ} (i : ℕ) (v0 : Vector UInt32 N),
          rootsInner wm 0 0 i v0 = v0 := fun wm _ i v0 => by unfold rootsInner; rfl
      unfold ensureRoots.outer
      split_ifs with h_gt
      · rfl
      · simp only [h_half_eq, h_inner_id, h_shift_eq,
          ih _ 63 hs_gt_K (by omega),
          Vector.getElem_set,
          show (0 : ℕ) ≠ 2 ^ K + j from by omega, if_false]

/-- `toMont a` computes `a.toNat * montR1.toNat % mod32.toNat` at the Nat level. -/
lemma to_mont_nat_helper (x a : ℕ) (hx_lt : x < mod32.toNat)
    (h_cong : x * 2 ^ 32 % mod32.toNat = a * (2 ^ 64 % mod32.toNat) % mod32.toNat) :
    x = a * montR1.toNat % mod32.toNat := by
  have hp : mod32.toNat = 3221225473 := rfl
  have hR1 : montR1.toNat = 1073741823 := rfl
  have hR2 : (2^64 % mod32.toNat) = 1789569709 := by decide
  rw [hR2] at h_cong
  rw [hp] at h_cong ⊢; rw [hR1]
  have h_rel : a * 1789569709 % 3221225473 = (a * 1073741823) * 2^32 % 3221225473 := by
    have : 1789569709 % 3221225473 = (1073741823 * 2^32) % 3221225473 := by decide
    rw [Nat.mul_mod, this, ← Nat.mul_mod, Nat.mul_assoc]
  have h1 : x * 2^32 ≡ (a * 1073741823) * 2^32 [MOD 3221225473] := by
    rw [Nat.ModEq]; rw [h_cong, h_rel]
  have h_coprime : Nat.gcd 3221225473 (2^32) = 1 := by decide
  exact (Nat.mod_eq_of_lt (hp ▸ hx_lt)).symm ▸ (Nat.ModEq.cancel_right_of_coprime h_coprime h1)

lemma to_mont_nat (a : UInt32) (ha : a.toNat < mod32.toNat) :
    (toMont a).toNat = a.toNat * montR1.toNat % mod32.toNat := by
  exact to_mont_nat_helper _ _ (to_mont_correct a ha).1 (to_mont_correct a ha).2

/-- Casting a UInt64 value below 2^32 to UInt32 and back preserves the Nat value. -/
lemma UInt64_toUInt32_toNat (x : UInt64) (hx : x.toNat < 2 ^ 32) :
    x.toUInt32.toNat = x.toNat := by
  simp_all only [Nat.reducePow, UInt64.toNat_toUInt32, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
    Nat.reduceAdd]

/--
The s = K base step of ensure_roots_outer_inv: after one outer-loop iteration at level K,
followed by any number of further iterations, position 2^K+j holds (w^j · montR1) % mod64.
-/
lemma ensure_roots_base_case (n : ℕ) (hN : 0 < n)
    (v : Vector UInt32 n) (K j f : ℕ)
    (hlen_K : 2 ^ (K + 1) ≤ n) (hj : j < 2 ^ K) (hK63 : K < 63)
    (h_half : ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat < n)
    (hlt : 2 ^ K + j < n) :
    let wm := toMont
      ((powModU64 primRoot ((mod64 - 1) / (2 ^ (K + 1) : ℕ).toUInt64) mod64).toUInt32)
    let vr := rootsInner wm ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat
        (((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat - 1) 0
        (v.set ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat montR1 h_half)
    let res := ensureRoots.outer n vr ((2 ^ (K + 2) : ℕ).toUInt64) hN f
    (res[2 ^ K + j]'hlt).toNat =
      ((primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1))) % mod64.toNat) ^ j *
        montR1.toNat % mod64.toNat := by
  -- unfold let wm, vr, res so we can work with the concrete terms
  simp only
  have h_halfLen : ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat = 2 ^ K :=
    pow2_toUInt64_halfLen K hK63
  have hlen_toNat : ((2 ^ (K + 1) : ℕ).toUInt64).toNat = 2 ^ (K + 1) :=
    nat_toUInt64_faithful _ (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have he_toNat : ((mod64 - 1) / (2 ^ (K + 1) : ℕ).toUInt64).toNat =
      (mod64.toNat - 1) / 2 ^ (K + 1) := by
    rw [UInt64.toNat_div, (by decide : (mod64 - 1).toNat = mod64.toNat - 1), hlen_toNat]
  have hpow_val : (powModU64 primRoot ((mod64 - 1) / (2 ^ (K + 1) : ℕ).toUInt64) mod64).toNat =
      primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1)) % mod64.toNat :=
    (powmod_correct _ _ _ (by decide) (by decide)).trans (by rw [he_toNat])
  have hpow_lt :
      (powModU64 primRoot ((mod64 - 1) / (2 ^ (K + 1) : ℕ).toUInt64) mod64).toNat < 2 ^ 32 := by
    rw [hpow_val]; exact (Nat.mod_lt _ (by decide)).trans (by decide)
  have hpow_u32 :
      (powModU64 primRoot ((mod64 - 1) / (2 ^ (K + 1) : ℕ).toUInt64) mod64).toUInt32.toNat =
      primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1)) % mod64.toNat :=
    (UInt64_toUInt32_toNat _ hpow_lt).trans hpow_val
  have hw_lt : primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1)) % mod64.toNat < mod32.toNat := by
    rw [← mod32_eq_mod]; exact Nat.mod_lt _ (by decide)
  have hwm :
      (toMont ((powModU64 primRoot
          ((mod64 - 1) / (2 ^ (K + 1) : ℕ).toUInt64) mod64).toUInt32)).toNat =
      primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1)) % mod64.toNat *
        montR1.toNat % mod32.toNat := by
    rw [to_mont_nat _ (hpow_u32 ▸ hw_lt), hpow_u32]
  let wm := toMont ((powModU64 primRoot ((mod64 - 1) / (2 ^ (K + 1) : ℕ).toUInt64) mod64).toUInt32)
  let v' := v.set ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat montR1 h_half
  let inner_v := rootsInner wm ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat
      (((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat - 1) 0 v'
  rw [outer_preserves_target n hN inner_v (K + 1) f K j (by omega) hj hlt (by omega)]
  have h_inner_bound : ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat +
      (((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat - 1) < n := by
    rw [h_halfLen]
    have h2K := Nat.two_pow_pos K
    have h2K1 : 2 ^ (K + 1) = 2 ^ K + 2 ^ K := by ring
    omega
  have hrmp := rootsInner_montPow wm ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat
      (((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat - 1) j v' (by rw [h_halfLen]; omega) h_inner_bound
  rw [show inner_v[2 ^ K + j]'hlt = inner_v[((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat + j]'(by omega)
      from by congr 1; omega]
  rw [hrmp]
  rw [show v'[((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat]'h_half = montR1 from by
        simp only [Nat.toUInt64_eq, UInt64.toNat_div, UInt64.toNat_ofNat', Nat.reducePow,
          UInt64.reduceToNat, Vector.getElem_set_self, v']]
  rw [montPow_spec wm _ j hwm, ← mod32_eq_mod]


/-
`toMont a` produces `(a.toNat * montR1.toNat) % mod32.toNat` when `a < mod32`.
-/
lemma to_mont_mont_r1 (a : UInt32) (ha : a.toNat < mod32.toNat) :
    (toMont a).toNat = (a.toNat * montR1.toNat) % mod32.toNat := by
  convert mont_mul_eq_nat a montR2 ha (by decide) using 1
  · rfl
  generalize_proofs at *
  unfold montMulNat; norm_num [MONT_PPRIME_spec, MONT_R2_spec, MONT_R1_spec] 
  norm_num [show mod64.toNat = 3 * 2 ^ 30 + 1 by rfl, show montPprime.toNat = 3221225471 by rfl]
  rw [show mod32.toNat = 3221225473 by rfl] ; omega

/-
Generalized loop invariant for `ensureRoots.outer`:
When started from vector `v`, current `len`, and fuel `f`,
position `2^K + j` gets the correct root value, provided:
- `2^(s+1) = len` (current len is `2^(s+1)` with `s ≤ K`)
- `K - s < f` (enough fuel to reach level K)
- `2^(K+1) ≤ n` (level K fits in the vector)
- positions below `2^s` in `v` may contain anything
-/
lemma ensure_roots_outer_inv (n : ℕ) (hN : 0 < n)
    (v : Vector UInt32 n) (s f K j : ℕ)
    (hlen_K : 2 ^ (K + 1) ≤ n) (hj : j < 2 ^ K)
    (hsK : s ≤ K) (hf : K < s + f)
    (hK63 : K < 63)
    :
    let w := (primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1))) % mod64.toNat
    have hlt : 2 ^ K + j < n := by nlinarith [pow_succ 2 K]
    ((ensureRoots.outer n v ((2 ^ (s + 1) : ℕ).toUInt64) hN f)[2 ^ K + j]'hlt).toNat =
      (w ^ j * montR1.toNat) % mod64.toNat := by
  simp only
  induction f generalizing v s with
  | zero => omega
  | succ f ih =>
    by_cases hsk : s = K
    · -- Base case: s = K. subst eliminates K, replacing it with s throughout.
      subst hsk
      -- After subst: hlen_K : 2^(s+1) ≤ n.toNat, hj : j < 2^s, goal uses s not K.
      have hs63 : s < 63 := by omega
      have h_half : ((2 ^ (s + 1) : ℕ).toUInt64 / 2).toNat < n := by
        rw [pow2_toUInt64_halfLen s hs63]; nlinarith [Nat.two_pow_pos s, pow_succ 2 s]
      have hlt : 2 ^ s + j < n := by nlinarith [pow_succ 2 s]
      unfold ensureRoots.outer
      split_ifs with h_gt
      · exact absurd h_gt (pow2_toUInt64_le_nat s n (by omega) hlen_K)
      · simp only [pow2_toUInt64_shift s hs63]
        exact ensure_roots_base_case n hN v s j f hlen_K hj hs63 h_half hlt
    · -- Inductive case: s < K, so the outer step at level s does not affect 2^K+j.
      -- Unfold one step, rewrite len <<< 1 to 2^(s+2), apply IH with s+1.
      have hs_lt : s < K := Nat.lt_of_le_of_ne hsK hsk
      have hs63 : s < 63 := by omega
      have h_sn : 2 ^ (s + 1) ≤ n :=
        Nat.le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hlen_K
      unfold ensureRoots.outer
      split_ifs with h_gt
      · exact absurd h_gt (pow2_toUInt64_le_nat s n (by omega) h_sn)
      · simp only [pow2_toUInt64_shift s hs63]
        exact ih _ (s + 1) (by omega) (by omega)

/-
The `ensureRoots.outer` loop, started from an all-zero vector with `len = 2` and
64 fuel steps, places `(w ^ j * montR1.toNat) % mod64` at position `2^K + j`
(for `2^(K+1) ≤ n` and `j < 2^K`), where `w = primRoot ^ ((mod64−1) / 2^(K+1)) % mod64`.
-/
lemma ensure_roots_outer_geom (n : ℕ) (hN : 0 < n)
    (K j : ℕ) (hK63 : K < 63) (hlen : 2 ^ (K + 1) ≤ n) (hj : j < 2 ^ K) :
    let w := (primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1))) % mod64.toNat
    have hlt : 2 ^ K + j < n := by nlinarith [pow_succ 2 K]
    ((ensureRoots.outer n (Vector.replicate n (0 : UInt32)) 2 hN 64)[2 ^ K + j]).toNat =
      (w ^ j * montR1.toNat) % mod64.toNat := by
  have h2 : 2 ^ (0 + 1) ≤ n := by
    simp only [zero_add, pow_one]
    exact le_trans (Nat.le_of_dvd (by omega) ⟨2^K, by ring⟩) hlen
  exact ensure_roots_outer_inv n hN _ 0 64 K j hlen hj (by omega) (by omega) hK63

theorem ensure_roots_spec (n : ℕ) (k j : ℕ)
    (hk63 : k < 63) (hlen_le : 2 ^ (k + 1) ≤ n) (hj : j < 2 ^ k) :
    let w := (primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (k + 1))) % mod64.toNat
    have : 2 ^ k + j < n := by nlinarith [pow_succ 2 k]
    (ensureRoots n)[2 ^ k + j] |>.toNat = (w ^ j * montR1.toNat) % mod64.toNat := by
  simp only
  have hn0' : n ≠ 0 := by
    have hpos : 0 < 2 ^ (k + 1) := by positivity
    omega
  -- `this : 2^k+j < n.toNat` is in scope from the `have` in the theorem statement.
  -- Universally quantify over the positivity proof to avoid proof-irrelevance issues.
  suffices h : ∀ (hN : 0 < n),
      let w := (primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (k + 1))) % mod64.toNat
      have hlt : 2 ^ k + j < n := by nlinarith [pow_succ 2 k]
      ((ensureRoots.outer n (Vector.replicate n (0 : UInt32)) 2 hN 64)[2 ^ k + j]).toNat =
        (w ^ j * montR1.toNat) % mod64.toNat by
    simp only [ensureRoots, dif_neg hn0']
    exact h _
  intro hN
  exact ensure_roots_outer_geom n hN k j hk63 hlen_le hj


end
