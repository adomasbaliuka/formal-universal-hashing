/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Log
import all Init.Data.Nat.Power2.Basic

/-! # Lemmas about `Nat.nextPowerOfTwo` -/

private lemma go_ge (n power : ℕ) (h : power > 0) :
    n ≤ Nat.nextPowerOfTwo.go n power h := by
  rw [Nat.nextPowerOfTwo.go]
  split
  · exact go_ge n (power * 2) (by positivity)
  · omega
termination_by n - power
decreasing_by omega

private lemma go_le (n power : ℕ) (h : power > 0) (j : ℕ)
    (hn : n ≤ 2 ^ j) (hp : power ≤ 2 ^ j) (hpow : power.isPowerOfTwo) :
    Nat.nextPowerOfTwo.go n power h ≤ 2 ^ j := by
  rw [Nat.nextPowerOfTwo.go]
  split
  · rename_i hlt
    obtain ⟨k, rfl⟩ := hpow
    have hkj : k < j := by
      by_contra hc
      push Not at hc
      exact not_lt.mpr (Nat.pow_le_pow_right (by omega) hc) (lt_of_lt_of_le hlt hn)
    have hpow2 : 2 ^ k * 2 = 2 ^ (k + 1) := by ring
    have hle : 2 ^ (k + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    exact go_le n (2 ^ k * 2) (by positivity) j hn
      (hpow2 ▸ hle) (Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo ⟨k, rfl⟩)
  · exact hp
termination_by n - power
decreasing_by omega

public lemma nextPow2_nat_ge (n : ℕ) : n ≤ Nat.nextPowerOfTwo n :=
  go_ge n 1 (by omega)

public lemma nextPow2_nat_le (n j : ℕ) (hn : n ≤ 2 ^ j) : Nat.nextPowerOfTwo n ≤ 2 ^ j :=
  go_le n 1 (by omega) j hn (Nat.one_le_pow j 2 (by omega)) Nat.isPowerOfTwo_one

private lemma lt_two_iff (x : ℕ) : x < 2 ↔ x ≤ 1 := by omega

public lemma nextPowerOfTwo_eq_two_pow_clog (n : ℕ) : n.nextPowerOfTwo = 2 ^ Nat.clog 2 n := by
  have hle := nextPow2_nat_ge n
  obtain ⟨k, hk⟩ := Nat.isPowerOfTwo_nextPowerOfTwo n
  rw [hk]
  simp_all only [lt_two_iff, zero_le, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, pow_right_inj₀]
  apply_fun Nat.clog 2 at hle using Nat.clog_monotone 2
  have clogpow (k : ℕ) : Nat.clog 2 (2 ^ k) = k := by
    simp_all only [lt_two_iff, le_refl, Nat.clog_pow]
  rw [clogpow] at hle
  suffices k ≤ Nat.clog 2 n by linarith
  have : n.nextPowerOfTwo ≤ 2 ^ Nat.clog 2 n :=
    (nextPow2_nat_le n <| Nat.clog 2 n) <| Nat.le_pow_clog (by decide) n
  rw [hk] at this
  apply_fun Nat.clog 2 at this using Nat.clog_monotone 2
  simpa [clogpow] using this
