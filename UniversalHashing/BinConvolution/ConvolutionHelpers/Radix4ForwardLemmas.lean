/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith.Frontend
import UniversalHashing.BinConvolution.ConvolutionHelpers.MontgomeryLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.RootTableLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.NttBoundLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.DFTLemmas
import UniversalHashing.BinConvolution.ConvolutionDefs

/-!
# Radix-4 forward butterfly

`ntt_roots_correct`, the `radix2Pass` correctness lemmas, and the forward radix-4 butterfly
(`butterfly4_forward_*`) culminating in `butterfly4_forward_ZMod_combined`. Split out of the
former `SolutionHelpers.lean`.
-/


/-- A root table is correct for an `m`-point NTT when every entry at index `len/2 + j`
    holds the twiddle factor `ω_{len}^j` in the Montgomery domain (multiplied by R),
    where `ω_{len} = primRoot ^ ((mod64 - 1) / len)` is a primitive `len`-th root of unity
    and R = montR1 = 2^32 mod mod64. -/
def ntt_roots_correct (m : ℕ) (roots : Vector UInt32 m) : Prop :=
  ∀ (len j : ℕ), 2 ≤ len → len ∣ m → j < len / 2 →
    (hbound : len / 2 + j < m) →
    ((roots[len / 2 + j]'hbound).toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j) *
      (montR1.toNat : ZMod mod32.toNat)

-- Divisors of 2^N that are ≥ 2 are themselves powers of 2 with exponent ≥ 1.
lemma pow2_dvd_is_pow2 (len N : ℕ) (hdvd : len ∣ 2 ^ N) (hlen : 2 ≤ len) :
    ∃ k : ℕ, len = 2 ^ (k+1) := by
  rw [Nat.dvd_prime_pow (by decide : Nat.Prime 2)] at hdvd
  obtain ⟨i, _, rfl⟩ := hdvd
  cases i with
  | zero => simp at hlen
  | succ i => exact ⟨i, rfl⟩

-- Cast of (w^j * montR1 % mod64) into ZMod equals primRoot^(e*j) * montR1.
lemma ensure_roots_zmod_cast (k j : ℕ) :
    let w := (primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (k + 1))) % mod64.toNat
    ((w ^ j * montR1.toNat % mod64.toNat : ℕ) : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ (k + 1) * j) *
      (montR1.toNat : ZMod mod32.toNat) := by
  simp only
  rw [mod32_eq_mod, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow,
      ZMod.natCast_mod, Nat.cast_pow, ← pow_mul]

/-- `ensureRoots m` produces a correct NTT root table for an `m`-point NTT. -/
lemma ensure_roots_ntt_correct {m : ℕ}
    (hm_pow2 : Nat.isPowerOfTwo m)
    (hm_dvd : m ∣ mod64.toNat - 1)
    :
    ntt_roots_correct m (ensureRoots m) := by
  intro len j hlen hdvd hj hbound
  obtain ⟨N, hN⟩ := hm_pow2
  rw [hN] at hdvd
  obtain ⟨k, hlen_eq⟩ := pow2_dvd_is_pow2 len N hdvd hlen
  have hlend2 : len / 2 = 2^k := by omega
  have hle : 2^(k+1) ≤ m := by
    rw [hN]; exact Nat.le_of_dvd (Nat.two_pow_pos N) (hlen_eq ▸ hdvd)
  have hj' : j < 2^k := by rwa [hlend2] at hj
  -- Derive k < 63 from m ∣ mod64.toNat - 1 (so m ≤ mod64.toNat - 1 < 2^64)
  have hk63 : k < 63 := by
    have hm_le : m ≤ mod64.toNat - 1 := Nat.le_of_dvd (by decide) hm_dvd
    have hm_lt : m < 2^64 := Nat.lt_of_le_of_lt hm_le (by decide)
    have h2k_lt : 2^(k+1) < 2^64 := Nat.lt_of_le_of_lt hle hm_lt
    have h := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2k_lt
    omega
  have hspec := ensure_roots_spec m k j hk63 hle hj'
  simp only at hspec
  have hlt : 2^k + j < m := by nlinarith [Nat.two_pow_pos k]
  have h_idx : (ensureRoots m)[len / 2 + j]'hbound = (ensureRoots m)[2^k + j]'hlt := by
    congr 1; omega
  rw [h_idx, hspec, hlen_eq]
  exact ensure_roots_zmod_cast k j

/-
After `toMont`, each element is `v[j] * montR1` in ZMod.  Factoring montR1 out of
    the DFT sum gives the main theorem's right-hand side.
-/
lemma to_mont_dft_factor {m : ℕ}
    (v : Vector UInt32 m)
    (hv_bound : v.all (· < mod32))
    (ω : ZMod mod32.toNat) (k : ℕ) :
    ∑ j : Fin m,
      ((toMont (v[j.val])).toNat : ZMod mod32.toNat) * ω ^ (j.val * k) =
    (montR1.toNat : ZMod mod32.toNat) * ∑ j : Fin m,
      (v[j.val].toNat : ZMod mod32.toNat) * ω ^ (j.val * k) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi_bound : v[i.val].toNat < mod32.toNat := by
    simp only [Vector.all_eq_true] at hv_bound
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using hv_bound i.val i.isLt)
  rw [to_mont_ZMod _ hi_bound]; ring

/-
`radix2Pass` does not modify elements outside the range `[2*i, 2*(i+k)-1]`.
-/
lemma radix2Pass_preserves {n : ℕ} (k i : ℕ)
    (a : Vector UInt32 n) (idx : ℕ) (hidx : idx < n)
    (h_below : idx < 2 * i ∨ idx ≥ 2 * (i + k)) :
    (radix2Pass k i a).get ⟨idx, hidx⟩ = a.get ⟨idx, hidx⟩ := by
  cases h_below <;> simp_all only [Vector.get_eq_getElem]
  · induction k generalizing i a with
    | zero => rfl
    | succ k ih =>
      simp only [radix2Pass]
      rw [ih (i + 1) _ (by omega)]
      split_ifs <;> first | rfl | (rw [Vector.getElem_set_ne, Vector.getElem_set_ne] <;> omega)
  · -- By induction on $k$: elements outside the range $[2i, 2(i+k)-1]$ remain unchanged.
    induction k generalizing i a idx with
    | zero => rfl
    | succ k ih =>
      simp only [radix2Pass]
      rw [ih (i + 1) _ idx hidx (by omega)]
      split_ifs <;> first | rfl | (rw [Vector.getElem_set_ne, Vector.getElem_set_ne] <;> omega)

/-
Correctness of `radix2Pass`: after processing `n/2` pairs starting from index 0,
    each pair is replaced by its sum and difference in ZMod arithmetic.
    Specifically, for each pair index `p < n/2`:
    - result[2p] = a[2p] + a[2p+1]  (mod mod32)
    - result[2p+1] = a[2p] - a[2p+1] (mod mod32)

After `radix2Pass`, the value at position `2*p` for pair `p` equals
    `addMod32(original[2p], original[2p+1])`.
-/
lemma radix2Pass_get_lo {n : ℕ} (k i : ℕ)
    (a : Vector UInt32 n) (p : ℕ)
    (hp : 2 * p + 1 < n) (hpi : i ≤ p) (hpk : p < i + k) (hk : i + k ≤ n / 2) :
    (radix2Pass k i a).get ⟨2 * p, by omega⟩ =
      addMod32 (a.get ⟨2 * p, by omega⟩) (a.get ⟨2 * p + 1, hp⟩) := by
  induction k generalizing i a p with
  | zero => linarith
  | succ k ih =>
    by_cases h : 2 * i < n ∧ 2 * i + 1 < n
    · by_cases hpi' : i = p
      · unfold radix2Pass
        rw [radix2Pass_preserves]
        · split_ifs <;> simp_all [Vector.get]
        · omega
      · specialize ih (i + 1)
            (if h1 : 2 * i < n then
                if h2 : 2 * i + 1 < n then
                  (a.set (2 * i)
                    (addMod32 (a.get ⟨2 * i, h1⟩)
                      (a.get ⟨2 * i + 1, h2⟩)) h1
                ).set (2 * i + 1)
                    (subMod32 (a.get ⟨2 * i, h1⟩)
                      (a.get ⟨2 * i + 1, h2⟩)) h2
                else a else a)
            p hp (by omega) (by omega) (by omega)
        simp_all [radix2Pass]
        simp [Vector.get, Vector.set]
        grind
    · omega

/-
After `radix2Pass`, the value at position `2*p+1` for pair `p` equals
    `subMod32(original[2p], original[2p+1])`.
-/
lemma radix2Pass_get_hi {n : ℕ} (k i : ℕ)
    (a : Vector UInt32 n) (p : ℕ)
    (hp : 2 * p + 1 < n) (hpi : i ≤ p) (hpk : p < i + k) (hk : i + k ≤ n / 2) :
    (radix2Pass k i a).get ⟨2 * p + 1, hp⟩ =
      subMod32 (a.get ⟨2 * p, by omega⟩) (a.get ⟨2 * p + 1, hp⟩) := by
  induction k generalizing i a with
  | zero => linarith
  | succ k ih =>
    by_cases h : p = i
    · rw [radix2Pass]
      split_ifs <;> simp_all only []
      · rw [radix2Pass_preserves]
        · simp [Vector.get]
        · omega
      · omega
      · omega
    · unfold radix2Pass; simp only [*]
      convert ih (i + 1) _ _ _ _ using 1
      · split_ifs <;> simp_all [Vector.get]
        grind
      · exact Nat.succ_le_of_lt (lt_of_le_of_ne hpi (Ne.symm h))
      · all_goals omega
      · omega

/-
Correctness of `radix2Pass`: after processing `n/2` pairs starting from index 0,
    each pair is replaced by its sum and difference in ZMod arithmetic.
    Specifically, for each pair index `p < n/2`:
    - result[2p] = a[2p] + a[2p+1]  (mod mod32)
    - result[2p+1] = a[2p] - a[2p+1] (mod mod32)
-/
lemma radix2Pass_ZMod_pair {n : ℕ} (a : Vector UInt32 n)
    (ha : a.all (· < mod32)) (p : ℕ) (hp : 2 * p + 1 < n) :
    let result := radix2Pass (n / 2) 0 a
    ((result.get ⟨2 * p, by omega⟩).toNat : ZMod mod32.toNat) =
      ((a.get ⟨2 * p, by omega⟩).toNat : ZMod mod32.toNat) +
      (a.get ⟨2 * p + 1, hp⟩).toNat ∧
    ((result.get ⟨2 * p + 1, hp⟩).toNat : ZMod mod32.toNat) =
      ((a.get ⟨2 * p, by omega⟩).toNat : ZMod mod32.toNat) -
      (a.get ⟨2 * p + 1, hp⟩).toNat := by
  constructor
  · rw [radix2Pass_get_lo]
    any_goals omega
    apply addmod32_ZMod
    · simp_all only [Vector.all_eq_true, decide_eq_true_eq]
      exact ha _ (by linarith)
    · rw [Vector.all_eq_true] at ha
      simpa using ha _ hp
  · convert submod32_ZMod _ _ _ _ using 1
    · convert congr_arg (fun x : UInt32 => (x.toNat : ZMod mod32.toNat))
          (radix2Pass_get_hi (n / 2) 0 a p hp (by omega) (by omega) (by omega)) using 1
    · simp_all only [Vector.all_eq_true, decide_eq_true_eq]
      exact ha _ (by linarith)
    · simp_all only [Vector.all_eq_true, decide_eq_true_eq]
      exact ha _ hp

/-
  Level 3a – algebraic property of ω.
  ω = primRoot^((p-1)/m) satisfies ω^(m/2) = -1 in ZMod p whenever m = 2^n with n ≥ 1
  and m ∣ p - 1.  This is the hypothesis required by `ref_ntt_eq_dft`.
  Proof sketch: primRoot is a primitive root mod p (`prim_root_PRIM_ROOT`),
  so ω^(m/2) = primRoot^((p-1)/2) = -1 by Euler's criterion.
  Since m = 2^n we have m/2 = 2^(n-1).
-/
lemma ω_is_primitive_half {m : UInt64} (n : ℕ)
    (hm_eq : m.toNat = 2 ^ n) (hm_dvd : m.toNat ∣ mod64.toNat - 1) :
    let ω : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m.toNat)
    n = 0 ∨ ω ^ 2 ^ (n - 1) = -1 := by
  simp only
  rcases n with _ | n
  · left; rfl
  · right
    simp only [Nat.succ_sub_one]
    rw [← pow_mul]
    -- Arithmetic: (mod64-1)/m * 2^n = (mod64-1)/2, using m = 2^(n+1) ∣ mod64-1
    have hdvd : 2 ^ (n + 1) ∣ mod64.toNat - 1 := hm_eq ▸ hm_dvd
    have harith : (mod64.toNat - 1) / m.toNat * 2 ^ n = (mod64.toNat - 1) / 2 := by
      rw [hm_eq]
      obtain ⟨c, hc⟩ := hdvd
      have h1 : (mod64.toNat - 1) / 2 ^ (n + 1) = c :=
        hc ▸ Nat.mul_div_cancel_left c (by positivity)
      have h2 : (mod64.toNat - 1) / 2 = c * 2 ^ n := by
        rw [hc, (by ring : 2 ^ (n + 1) = 2 * 2 ^ n),
            (by ring : 2 * 2 ^ n * c = 2 * (c * 2 ^ n)),
            Nat.mul_div_cancel_left _ (by norm_num)]
      rw [h1, h2, mul_comm]
    rw [harith]
    exact prim_root_half_eq_neg_one

/-- Nat version of ω_is_primitive_half: works when m : ℕ instead of UInt64. -/
lemma ω_is_primitive_half_nat (m n : ℕ) (hm_eq : m = 2 ^ n) (hm_dvd : m ∣ mod64.toNat - 1) :
    n = 0 ∨
    ((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)) ^ 2 ^ (n - 1) = -1 := by
  have hn : n < 64 := by
    have hm_le : m ≤ mod64.toNat - 1 := Nat.le_of_dvd (by decide) hm_dvd
    have hm_lt : m < 2 ^ 64 := Nat.lt_of_le_of_lt hm_le (by decide)
    have h2n_lt : 2 ^ n < 2 ^ 64 := hm_eq ▸ hm_lt
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2n_lt
  have hm_small : m < 2 ^ 64 := hm_eq ▸ Nat.pow_lt_pow_right (by norm_num) hn
  have hm_toNat : m.toUInt64.toNat = m := nat_toUInt64_faithful m hm_small
  have h := ω_is_primitive_half (m := m.toUInt64) n
    (by rw [hm_toNat]; exact hm_eq)
    (by rw [hm_toNat]; exact hm_dvd)
  simp only at h
  rwa [hm_toNat] at h

-- Helper: look up a root value via ntt_roots_correct at an explicit index.
-- `heq` proves `idx = len / 2 + j`; after subst the goal is exactly `hroots`.
lemma ntt_roots_correct_at {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots)
    (len j idx : ℕ) (h2 : 2 ≤ len) (hdvd : len ∣ N) (hj : j < len / 2)
    (hidx : idx < N) (heq : idx = len / 2 + j) :
    ((roots[idx]'hidx).toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j) *
        (montR1.toNat : ZMod mod32.toNat) := by
  subst heq; exact hroots len j h2 hdvd hj hidx

-- Helper: montMul ZMod when the right factor equals τ * 2^32.
-- Helper: montMul ZMod when the left factor equals τ * 2^32.
-- Helper: Vector.getD idx 0 = Vector[idx]'h when idx < N.
lemma vector_getD_eq_getElem {α : Type*} {N : ℕ} (v : Vector α N)
    (idx : ℕ) (h : idx < N) (default : α) :
    v.getD idx default = v[idx]'h := by
  unfold Vector.getD
  have ha : idx < v.toArray.size := by rw [v.size_toArray]; exact h
  rw [← Array.getElem_eq_getD (fallback := default) (h := ha)]
  exact Vector.getElem_toArray ha

/-
  Level 3c – Structural lemmas: what `butterfly4` returns at each output position.
-/

-- Shared expansion: unfolds butterfly4 (forward) into the explicit Vector.set chain once,
-- absorbing the expensive simp only [butterfly4, ...] cost for all four getElem_posX lemmas.
private lemma butterfly4_forward_expand {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (ht1 : s + j2 < N) (ht2 : len + j2 < N) (ht3 : len + j2 + s < N) :
    butterfly4 a false roots s len i2 j2 =
      let t1 := roots[s + j2]'ht1
      let t2 := roots[len + j2]'ht2
      let t3 := roots[len + j2 + s]'ht3
      let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
      let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
      let P  := addMod32 (a[i2 + j2]'hbnd0) aB
      let Rv := addMod32 (a[i2 + len + j2]'hbnd2) aD
      let Q  := subMod32 (a[i2 + j2]'hbnd0) aB
      let Sv := subMod32 (a[i2 + len + j2]'hbnd2) aD
      let t2R := montMul t2 Rv
      let t3S := montMul t3 Sv
      ((((a.set (i2 + j2) (addMod32 P t2R) hbnd0).set
              (i2 + len + j2) (subMod32 P t2R) hbnd2).set
              (i2 + j2 + s) (addMod32 Q t3S) hbnd1).set
              (i2 + len + j2 + s) (subMod32 Q t3S) hbnd3) := by
  simp only [butterfly4, Bool.not_false, ite_true,
    vector_getD_eq_getElem roots _ ht1 0, vector_getD_eq_getElem roots _ ht2 0,
    vector_getD_eq_getElem roots _ ht3 0,
    dif_pos hbnd0, dif_pos hbnd1, dif_pos hbnd2, dif_pos hbnd3,
    Vector.get_eq_getElem]

lemma butterfly4_forward_getElem_pos0 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (ht1 : s + j2 < N) (ht2 : len + j2 < N) (ht3 : len + j2 + s < N)
    (hne10 : i2 + j2 + s ≠ i2 + j2)
    (hne20 : i2 + len + j2 ≠ i2 + j2)
    (hne30 : i2 + len + j2 + s ≠ i2 + j2) :
    let t1 := roots[s + j2]'ht1
    let t2 := roots[len + j2]'ht2
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let P := addMod32 (a[i2 + j2]'hbnd0) aB
    let R_v := addMod32 (a[i2 + len + j2]'hbnd2) aD
    let t2R := montMul t2 R_v
    (butterfly4 a false roots s len i2 j2)[i2 + j2]'hbnd0 = addMod32 P t2R := by
  rw [butterfly4_forward_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3 ht1 ht2 ht3]
  simp only []
  rw [Vector.getElem_set, if_neg hne30, Vector.getElem_set, if_neg hne10,
      Vector.getElem_set, if_neg hne20, Vector.getElem_set_self]

lemma butterfly4_forward_getElem_pos2 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (ht1 : s + j2 < N) (ht2 : len + j2 < N) (ht3 : len + j2 + s < N)
    (hne12 : i2 + j2 + s ≠ i2 + len + j2)
    (hne32 : i2 + len + j2 + s ≠ i2 + len + j2) :
    let t1 := roots[s + j2]'ht1
    let t2 := roots[len + j2]'ht2
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let P := addMod32 (a[i2 + j2]'hbnd0) aB
    let R_v := addMod32 (a[i2 + len + j2]'hbnd2) aD
    let t2R := montMul t2 R_v
    (butterfly4 a false roots s len i2 j2)[i2 + len + j2]'hbnd2 = subMod32 P t2R := by
  rw [butterfly4_forward_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3 ht1 ht2 ht3]
  simp only []
  rw [Vector.getElem_set, if_neg hne32, Vector.getElem_set, if_neg hne12,
      Vector.getElem_set_self]

lemma butterfly4_forward_getElem_pos1 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (ht1 : s + j2 < N) (ht2 : len + j2 < N) (ht3 : len + j2 + s < N)
    (hne31 : i2 + len + j2 + s ≠ i2 + j2 + s) :
    let t1 := roots[s + j2]'ht1
    let t3 := roots[len + j2 + s]'ht3
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let Q := subMod32 (a[i2 + j2]'hbnd0) aB
    let S_v := subMod32 (a[i2 + len + j2]'hbnd2) aD
    let t3S := montMul t3 S_v
    (butterfly4 a false roots s len i2 j2)[i2 + j2 + s]'hbnd1 = addMod32 Q t3S := by
  rw [butterfly4_forward_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3 ht1 ht2 ht3]
  simp only []
  rw [Vector.getElem_set, if_neg hne31, Vector.getElem_set_self]

lemma butterfly4_forward_getElem_pos3 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (ht1 : s + j2 < N) (ht2 : len + j2 < N) (ht3 : len + j2 + s < N) :
    let t1 := roots[s + j2]'ht1
    let t3 := roots[len + j2 + s]'ht3
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let Q := subMod32 (a[i2 + j2]'hbnd0) aB
    let S_v := subMod32 (a[i2 + len + j2]'hbnd2) aD
    let t3S := montMul t3 S_v
    (butterfly4 a false roots s len i2 j2)[i2 + len + j2 + s]'hbnd3 = subMod32 Q t3S := by
  rw [butterfly4_forward_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3 ht1 ht2 ht3]
  simp only []
  rw [Vector.getElem_set_self]

/-
  Level 3d – Preservation lemmas: positions untouched by butterfly4 / radix4Inner / radix4Middle.
-/

/-- `butterfly4` only modifies the four butterfly positions; all other positions are unchanged. -/
lemma butterfly4_getElem_ne {N : ℕ} (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (i : ℕ) (hi : i < N)
    (hne0 : i2 + j2 ≠ i) (hne1 : i2 + j2 + s ≠ i)
    (hne2 : i2 + len + j2 ≠ i) (hne3 : i2 + len + j2 + s ≠ i) :
    (butterfly4 a false roots s len i2 j2)[i]'hi = a[i]'hi := by
  simp only [butterfly4, Bool.not_false, ite_true,
    dif_pos hbnd0, dif_pos hbnd1, dif_pos hbnd2, dif_pos hbnd3]
  rw [Vector.getElem_set, if_neg hne3, Vector.getElem_set, if_neg hne1,
      Vector.getElem_set, if_neg hne2, Vector.getElem_set, if_neg hne0]

/-- `radix4Inner` leaves position `hi` unchanged if it is not any of the four butterfly
    positions for any `j2` in the processed range `[j2_start, j2_start + k)`. -/
lemma radix4Inner_getElem_ne {N : ℕ} (roots a : Vector UInt32 N)
    (s len i2 : ℕ) (k j2_start : ℕ) (hi : ℕ) (hlt : hi < N)
    (hbnd : ∀ j2, j2_start ≤ j2 → j2 < j2_start + k →
      i2 + j2 < N ∧ i2 + j2 + s < N ∧
      i2 + len + j2 < N ∧ i2 + len + j2 + s < N)
    (hne : ∀ j2, j2_start ≤ j2 → j2 < j2_start + k →
      i2 + j2 ≠ hi ∧ i2 + j2 + s ≠ hi ∧
      i2 + len + j2 ≠ hi ∧ i2 + len + j2 + s ≠ hi) :
    (radix4Inner false roots s len i2 k j2_start a)[hi]'hlt = a[hi]'hlt := by
  induction k generalizing j2_start a with
  | zero => rfl
  | succ k ih =>
    have hb := hbnd j2_start (le_refl _) (by omega)
    have hn := hne  j2_start (le_refl _) (by omega)
    calc (radix4Inner false roots s len i2 (k + 1) j2_start a)[hi]'hlt
        = (radix4Inner false roots s len i2 k (j2_start + 1)
            (butterfly4 a false roots s len i2 j2_start))[hi]'hlt := rfl
      _ = (butterfly4 a false roots s len i2 j2_start)[hi]'hlt :=
            ih (butterfly4 a false roots s len i2 j2_start) (j2_start + 1)
               (fun j2 hlo hhi => hbnd j2 (by omega) (by omega))
               (fun j2 hlo hhi => hne  j2 (by omega) (by omega))
      _ = a[hi]'hlt :=
            butterfly4_getElem_ne roots a s len i2 j2_start
               hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hi hlt hn.1 hn.2.1 hn.2.2.1 hn.2.2.2

/-- `radix4Middle` leaves position `hi` unchanged if it is not any butterfly position for
    any group `b` in `[b_start, b_start + k)` and any `j2 < s`. -/
lemma radix4Middle_getElem_ne {N : ℕ} (roots a : Vector UInt32 N)
    (s len : ℕ) (k b_start : ℕ) (hi : ℕ) (hlt : hi < N)
    (hbnd : ∀ b, b_start ≤ b → b < b_start + k → ∀ j2, j2 < s →
      let i2 := b * 2 * len
      i2 + j2 < N ∧ i2 + j2 + s < N ∧
      i2 + len + j2 < N ∧ i2 + len + j2 + s < N)
    (hne : ∀ b, b_start ≤ b → b < b_start + k → ∀ j2, j2 < s →
      let i2 := b * 2 * len
      i2 + j2 ≠ hi ∧ i2 + j2 + s ≠ hi ∧
      i2 + len + j2 ≠ hi ∧ i2 + len + j2 + s ≠ hi) :
    (radix4Middle false roots s len k b_start a)[hi]'hlt = a[hi]'hlt := by
  induction k generalizing b_start a with
  | zero => rfl
  | succ k ih =>
    calc (radix4Middle false roots s len (k + 1) b_start a)[hi]'hlt
        = (radix4Middle false roots s len k (b_start + 1)
            (radix4Inner false roots s len
              (b_start * 2 * len) s 0 a))[hi]'hlt := rfl
      _ = (radix4Inner false roots s len
              (b_start * 2 * len) s 0 a)[hi]'hlt :=
            ih (radix4Inner false roots s len
                  (b_start * 2 * len) s 0 a)
               (b_start + 1)
               (fun b hblo hbhi j2 hj2 => hbnd b (by omega) (by omega) j2 hj2)
               (fun b hblo hbhi j2 hj2 => hne  b (by omega) (by omega) j2 hj2)
      _ = a[hi]'hlt :=
            radix4Inner_getElem_ne roots a s len
               (b_start * 2 * len) s 0 hi hlt
               (fun j2 _ hj2 => hbnd b_start (le_refl _) (by omega) j2 (by omega))
               (fun j2 _ hj2 => hne  b_start (le_refl _) (by omega) j2 (by omega))

/- Level 3e – Composition lemma: splitting radix4Inner into two sequential calls. -/

lemma radix4Inner_comp {N : ℕ} (roots : Vector UInt32 N) (inverse : Bool)
    (s len i2 : ℕ) (k1 k2 j2_start : ℕ) (a : Vector UInt32 N) :
    radix4Inner inverse roots s len i2 (k1 + k2) j2_start a =
    radix4Inner inverse roots s len i2 k2 (j2_start + k1)
      (radix4Inner inverse roots s len i2 k1 j2_start a) := by
  induction k1 generalizing j2_start a with
  | zero => simp only [radix4Inner, Nat.zero_add, Nat.add_zero]
  | succ k1 ih =>
    rw [show k1 + 1 + k2 = k1 + k2 + 1 by omega]
    simp only [radix4Inner]
    rw [ih (j2_start + 1) (butterfly4 a inverse roots s len i2 j2_start)]
    congr 1
    omega

/- Level 3f – butterfly4 ZMod-level correctness at the four output positions. -/

private lemma butterfly4_forward_idx_bounds_nat {N : ℕ} (s len j2 : ℕ)
    (hlen : len = 2 * s) (hlen_dvd : 2 * len ∣ N) (hj2 : j2 < s) (hN_pos : 0 < N) :
    s + j2 < N ∧ len + j2 < N ∧ len + j2 + s < N := by
  have h2len_le : 2 * len ≤ N := Nat.le_of_dvd hN_pos hlen_dvd
  omega

-- Root ZMod values for the three forward butterfly twiddle positions,
-- Element and root bounds for forward butterfly4 inputs, proved once for all pos lemmas.
private lemma butterfly4_forward_bounds {N : ℕ}
    (a : Vector UInt32 N) (ha : a.all (· < mod32))
    (roots : Vector UInt32 N) (hroots_bnd : roots.all (· < mod32))
    (i2 j2 s len : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (ht1 : s + j2 < N) (ht2 : len + j2 < N) (ht3 : len + j2 + s < N) :
    (a[i2 + j2]'hbnd0).toNat < mod32.toNat ∧
    (a[i2 + j2 + s]'hbnd1).toNat < mod32.toNat ∧
    (a[i2 + len + j2]'hbnd2).toNat < mod32.toNat ∧
    (a[i2 + len + j2 + s]'hbnd3).toNat < mod32.toNat ∧
    (roots[s + j2]'ht1).toNat < mod32.toNat ∧
    (roots[len + j2]'ht2).toNat < mod32.toNat ∧
    (roots[len + j2 + s]'ht3).toNat < mod32.toNat := by
  simp only [Vector.all_eq_true, decide_eq_true_eq] at ha hroots_bnd
  exact ⟨UInt32.lt_iff_toNat_lt.mp (ha _ hbnd0),
         UInt32.lt_iff_toNat_lt.mp (ha _ hbnd1),
         UInt32.lt_iff_toNat_lt.mp (ha _ hbnd2),
         UInt32.lt_iff_toNat_lt.mp (ha _ hbnd3),
         UInt32.lt_iff_toNat_lt.mp (hroots_bnd _ ht1),
         UInt32.lt_iff_toNat_lt.mp (hroots_bnd _ ht2),
         UInt32.lt_iff_toNat_lt.mp (hroots_bnd _ ht3)⟩

private lemma butterfly4_forward_ZMod_pos0 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hN_le : N ≤ 2 ^ 64) :
    ((butterfly4 a false roots s len i2 j2)[i2 + j2]'hbnd0).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
        (a[i2 + j2 + s]'hbnd1).toNat +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * j2) *
        ((a[i2 + len + j2]'hbnd2).toNat +
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have h_idx_bounds := butterfly4_forward_idx_bounds_nat s len j2 hlen hlen_dvd hj2 (by omega)
  have hlen_pos : len > 0 := by omega
  have hne10 : i2 + j2 + s ≠ i2 + j2 := by omega
  have hne20 : i2 + len + j2 ≠ i2 + j2 := by omega
  have hne30 : i2 + len + j2 + s ≠ i2 + j2 := by omega
  obtain ⟨ha0, ha1, ha2, ha3, hr1, hr2, _⟩ :=
    butterfly4_forward_bounds a ha roots hroots_bnd i2 j2 s len
      hbnd0 hbnd1 hbnd2 hbnd3
      h_idx_bounds.1 h_idx_bounds.2.1 h_idx_bounds.2.2
  rw [butterfly4_forward_getElem_pos0]
  any_goals (first | assumption | exact h_idx_bounds.1 |
    exact h_idx_bounds.2.1 | exact h_idx_bounds.2.2)
  rw [addmod32_ZMod, mont_mul_ZMod]
  · rw [addmod32_ZMod, addmod32_ZMod]
    · rw [mont_mul_ZMod, mont_mul_ZMod]
      · have h_root_values :
            ((roots[s + j2]'h_idx_bounds.left).toNat : ZMod mod32.toNat) =
              (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
              (montR1.toNat : ZMod mod32.toNat) ∧
            ((roots[len + j2]'h_idx_bounds.right.left).toNat : ZMod mod32.toNat) =
              (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * j2) *
              (montR1.toNat : ZMod mod32.toNat) := by
          apply And.intro
          · apply ntt_roots_correct_at
            · assumption
            · omega
            · exact dvd_of_mul_left_dvd hlen_dvd
            · omega
            · omega
          · convert ntt_roots_correct_at roots hroots (2 * len) j2 (len + j2) _ _ _ _ using 1
            any_goals omega
            simp
        rw [h_root_values.1, h_root_values.2, MONT_R1_ZMod]
        simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
          mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
        ring
      · exact ha3
      · exact hr1
      · exact ha1
      · exact hr1
    · exact ha2
    · apply mont_mul_lt_of_right; exact hr1
    · exact ha0
    · apply mont_mul_lt_of_left; exact ha1
  · exact hr2
  · apply addmod32_lt
    · exact ha2
    · apply mont_mul_lt_of_right; exact hr1
  · apply addmod32_lt
    · exact ha0
    · apply mont_mul_lt_of_left; exact ha1
  · apply mont_mul_lt_of_left; exact hr2

-- The ZMod correctness proof for butterfly4 at position 2 uses many rewriting steps.
private lemma butterfly4_forward_ZMod_pos2 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hN_le : N ≤ 2 ^ 64) :
    ((butterfly4 a false roots s len i2 j2)[i2 + len + j2]'hbnd2).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
        (a[i2 + j2 + s]'hbnd1).toNat -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * j2) *
        ((a[i2 + len + j2]'hbnd2).toNat +
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have h_idx_bounds := butterfly4_forward_idx_bounds_nat s len j2 hlen hlen_dvd hj2 (by omega)
  have hlen_pos : len > 0 := by omega
  have hne12 : i2 + j2 + s ≠ i2 + len + j2 := by omega
  have hne32 : i2 + len + j2 + s ≠ i2 + len + j2 := by omega
  obtain ⟨ha0, ha1, ha2, ha3, hr1, hr2, _⟩ :=
    butterfly4_forward_bounds a ha roots hroots_bnd i2 j2 s len
      hbnd0 hbnd1 hbnd2 hbnd3
      h_idx_bounds.1 h_idx_bounds.2.1 h_idx_bounds.2.2
  rw [butterfly4_forward_getElem_pos2 roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3
      h_idx_bounds.left h_idx_bounds.right.left h_idx_bounds.right.right hne12 hne32]
  rw [submod32_ZMod, mont_mul_ZMod]
  · rw [addmod32_ZMod, addmod32_ZMod]
    · rw [mont_mul_ZMod, mont_mul_ZMod]
      · have h_root_values :
              ((roots[s + j2]'h_idx_bounds.left).toNat : ZMod mod32.toNat) =
                (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
                (montR1.toNat : ZMod mod32.toNat) ∧
              ((roots[len + j2]'h_idx_bounds.right.left).toNat : ZMod mod32.toNat) =
                (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * j2) *
                (montR1.toNat : ZMod mod32.toNat) := by
            apply And.intro
            · apply ntt_roots_correct_at
              · assumption
              · omega
              · exact dvd_of_mul_left_dvd hlen_dvd
              · omega
              · omega
            · convert ntt_roots_correct_at roots hroots (2 * len) j2 (len + j2) _ _ _ _ using 1
              any_goals omega
              simp
        rw [h_root_values.1, h_root_values.2, MONT_R1_ZMod]
        simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
          mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
        ring
      · exact ha3
      · exact hr1
      · exact ha1
      · exact hr1
    · exact ha2
    · apply mont_mul_lt_of_right; exact hr1
    · exact ha0
    · apply mont_mul_lt_of_left; exact ha1
  · exact hr2
  · apply addmod32_lt
    · exact ha2
    · apply mont_mul_lt_of_right; exact hr1
  · apply addmod32_lt
    · exact ha0
    · apply mont_mul_lt_of_left; exact ha1
  · apply mont_mul_lt_of_left; exact hr2

-- The ZMod correctness proof for butterfly4 at position 1 uses many rewriting steps.
private lemma butterfly4_forward_ZMod_pos1 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hN_le : N ≤ 2 ^ 64) :
    ((butterfly4 a false roots s len i2 j2)[i2 + j2 + s]'hbnd1).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
        (a[i2 + j2 + s]'hbnd1).toNat +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (s + j2)) *
        ((a[i2 + len + j2]'hbnd2).toNat -
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have h_idx_bounds := butterfly4_forward_idx_bounds_nat s len j2 hlen hlen_dvd hj2 (by omega)
  have hlen_pos : len > 0 := by omega
  have hne31 : i2 + len + j2 + s ≠ i2 + j2 + s := by omega
  obtain ⟨ha0, ha1, ha2, ha3, hr1, _, hr3⟩ :=
    butterfly4_forward_bounds a ha roots hroots_bnd i2 j2 s len
      hbnd0 hbnd1 hbnd2 hbnd3
      h_idx_bounds.1 h_idx_bounds.2.1 h_idx_bounds.2.2
  rw [butterfly4_forward_getElem_pos1 roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3
      h_idx_bounds.left h_idx_bounds.right.left h_idx_bounds.right.right hne31]
  rw [addmod32_ZMod, mont_mul_ZMod]
  · rw [submod32_ZMod, submod32_ZMod]
    · rw [mont_mul_ZMod, mont_mul_ZMod]
      · have h_root_values :
              ((roots[s + j2]'h_idx_bounds.left).toNat : ZMod mod32.toNat) =
                (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
                (montR1.toNat : ZMod mod32.toNat) ∧
              ((roots[len + j2 + s]'h_idx_bounds.right.right).toNat : ZMod mod32.toNat) =
                (primRoot.toNat : ZMod mod32.toNat) ^
                ((mod64.toNat - 1) / (2 * len) * (s + j2)) *
                (montR1.toNat : ZMod mod32.toNat) := by
          apply And.intro
          · apply ntt_roots_correct_at
            · assumption
            · omega
            · exact dvd_of_mul_left_dvd hlen_dvd
            · omega
            · omega
          · convert ntt_roots_correct_at roots hroots (2 * len) (s + j2)
                  (len + j2 + s) _ _ _ _ using 1
            any_goals omega
            simp [add_comm, add_left_comm]
        rw [h_root_values.1, h_root_values.2, MONT_R1_ZMod]
        simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
          mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
        ring
      · exact ha3
      · exact hr1
      · exact ha1
      · exact hr1
    · exact ha2
    · apply mont_mul_lt_of_right; exact hr1
    · exact ha0
    · apply mont_mul_lt_of_left; exact ha1
  · exact hr3
  · apply submod32_lt
    · exact ha2
    · apply mont_mul_lt_of_right; exact hr1
  · apply submod32_lt
    · exact ha0
    · apply mont_mul_lt_of_left; exact ha1
  · apply mont_mul_lt_of_left; exact hr3

-- The ZMod correctness proof for butterfly4 at position 3 uses many rewriting steps.
private lemma butterfly4_forward_ZMod_pos3 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hN_le : N ≤ 2 ^ 64) :
    ((butterfly4 a false roots s len i2 j2)[i2 + len + j2 + s]'hbnd3).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
        (a[i2 + j2 + s]'hbnd1).toNat -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (s + j2)) *
        ((a[i2 + len + j2]'hbnd2).toNat -
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have h_idx_bounds := butterfly4_forward_idx_bounds_nat s len j2 hlen hlen_dvd hj2 (by omega)
  obtain ⟨ha0, ha1, ha2, ha3, hr1, _, hr3⟩ :=
    butterfly4_forward_bounds a ha roots hroots_bnd i2 j2 s len
      hbnd0 hbnd1 hbnd2 hbnd3
      h_idx_bounds.1 h_idx_bounds.2.1 h_idx_bounds.2.2
  rw [butterfly4_forward_getElem_pos3]
  any_goals tauto
  rw [submod32_ZMod, mont_mul_ZMod]
  · rw [submod32_ZMod, submod32_ZMod]
    · rw [mont_mul_ZMod, mont_mul_ZMod]
      · have h_root_values :
              ((roots[s + j2]'h_idx_bounds.left).toNat : ZMod mod32.toNat) =
                (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
                (montR1.toNat : ZMod mod32.toNat) ∧
              ((roots[len + j2 + s]'h_idx_bounds.right.right).toNat : ZMod mod32.toNat) =
                (primRoot.toNat : ZMod mod32.toNat) ^
                ((mod64.toNat - 1) / (2 * len) * (s + j2)) *
                (montR1.toNat : ZMod mod32.toNat) := by
          apply And.intro
          · apply ntt_roots_correct_at
            · assumption
            · omega
            · exact dvd_of_mul_left_dvd hlen_dvd
            · omega
            · omega
          · convert ntt_roots_correct_at roots hroots (2 * len) (s + j2)
                  (len + j2 + s) _ _ _ _ using 1
            any_goals omega
            simp [add_comm, add_left_comm]
        rw [h_root_values.1, h_root_values.2, MONT_R1_ZMod]
        simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
          mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
        ring
      · exact ha3
      · exact hr1
      · exact ha1
      · exact hr1
    · exact ha2
    · apply mont_mul_lt_of_right; exact hr1
    · exact ha0
    · apply mont_mul_lt_of_left; exact ha1
  · exact hr3
  · apply submod32_lt
    · exact ha2
    · apply mont_mul_lt_of_right; exact hr1
  · apply submod32_lt
    · exact ha0
    · apply mont_mul_lt_of_left; exact ha1
  · apply mont_mul_lt_of_left; exact hr3

lemma butterfly4_forward_ZMod_combined {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hN_le : N ≤ 2 ^ 64) :
    let τ₁ : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2)
    let τ₂ : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * j2)
    let τ₃ : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (s + j2))
    let r  := butterfly4 a false roots s len i2 j2
    let A₀ := ((a[i2 + j2]'hbnd0).toNat       : ZMod mod32.toNat)
    let A₁ := ((a[i2 + j2 + s]'hbnd1).toNat   : ZMod mod32.toNat)
    let A₂ := ((a[i2 + len + j2]'hbnd2).toNat : ZMod mod32.toNat)
    let A₃ := ((a[i2 + len + j2 + s]'hbnd3).toNat : ZMod mod32.toNat)
    ((r[i2 + j2]'hbnd0).toNat           : ZMod mod32.toNat) =
        A₀ + τ₁ * A₁ + τ₂ * (A₂ + τ₁ * A₃) ∧
    ((r[i2 + len + j2]'hbnd2).toNat     : ZMod mod32.toNat) =
        A₀ + τ₁ * A₁ - τ₂ * (A₂ + τ₁ * A₃) ∧
    ((r[i2 + j2 + s]'hbnd1).toNat       : ZMod mod32.toNat) =
        A₀ - τ₁ * A₁ + τ₃ * (A₂ - τ₁ * A₃) ∧
    ((r[i2 + len + j2 + s]'hbnd3).toNat : ZMod mod32.toNat) =
        A₀ - τ₁ * A₁ - τ₃ * (A₂ - τ₁ * A₃) := by
  simp only []
  exact ⟨butterfly4_forward_ZMod_pos0 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hj2 hbnd0 hbnd1 hbnd2 hbnd3 hN_le,
  butterfly4_forward_ZMod_pos2 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hj2 hbnd0 hbnd1 hbnd2 hbnd3 hN_le,
  butterfly4_forward_ZMod_pos1 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hj2 hbnd0 hbnd1 hbnd2 hbnd3 hN_le,
  butterfly4_forward_ZMod_pos3 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hj2 hbnd0 hbnd1 hbnd2 hbnd3 hN_le⟩

