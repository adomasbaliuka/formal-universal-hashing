/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Star.Real

/-!
# Utility lemmas

-/

section Util

/--
`exp(-x) ≤ 1 - x + x²/2 for x ≥ 0`.
Second-order Taylor upper bound for exp(-x).
-/
lemma exp_neg_le_one_sub_add_sq_div_two (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have h_exp : Real.exp x ≥ 1 + x + x ^ 2 / 2 :=
    Real.quadratic_le_exp_of_nonneg hx
  rw [Real.exp_neg]
  nlinarith [mul_inv_cancel₀ (show Real.exp x ≠ 0 by positivity), sq_nonneg (x - 1)]

/--
`(1 - p) ^ t ≤ exp(-p * t)` for `0 ≤ p, p ≤ 1`, and `t ≥ 0`.
-/
lemma rpow_one_sub_le_exp_neg (p t : ℝ) (hp1 : p ≤ 1) (ht : 0 ≤ t) :
    (1 - p) ^ t ≤ Real.exp (-p * t) := by
  rw [Real.rpow_def_of_nonneg] <;> norm_num <;> try linarith
  split_ifs
  · simp_all
  · simp_all only [Real.exp_neg, inv_nonneg]
    positivity
  · exact Real.exp_le_exp.mpr (by
      nlinarith [Real.log_le_sub_one_of_pos (
        show 0 < 1 - p by exact lt_of_le_of_ne (by linarith) (Ne.symm ‹_›))])

/--
Second-order quadratic upper bound: `(1 - p) ^ t ≤ 1 - p*t + (p*t)²/2` for `0 ≤ p ≤ 1` and `t ≥ 0`.
-/
lemma rpow_upper_bound_quadratic (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 ≤ t) :
    (1 - p) ^ t ≤ 1 - p * t + (p * t) ^ 2 / 2 := by
  calc (1 - p) ^ t ≤ Real.exp (-p * t) :=
          rpow_one_sub_le_exp_neg p t hp1 ht
    _ ≤ 1 - (p * t) + (p * t) ^ 2 / 2 := by
          rw [show -p * t = -(p * t) from by ring]
          exact exp_neg_le_one_sub_add_sq_div_two (p * t) (mul_nonneg hp0 ht)

/-- s² + 2s - 1 ≤ 0 when 0 ≤ s ≤ √2 - 1.
The quadratic s² + 2s - 1 = (s + 1)² - 2 has positive root √2 - 1. -/
lemma quadratic_le_zero_of_le_sqrt_two_sub_one (s : ℝ) (hs0 : 0 ≤ s)
    (hs : s ≤ Real.sqrt 2 - 1) : s ^ 2 + 2 * s - 1 ≤ 0 := by
  nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num)]

/--
Lemma 21 from Pǎtraşcu and Thorup, "The Power of Simple Tabulation Hashing" (arXiv:1011.5200).
The paper states a strict inequality, but the proof only establishes `≥`: equality holds at the
boundary cases p = 0 or k = 0.
-/
theorem one_sub_ge_rpow_of_pk_le_sqrt2_sub_one (p k : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (gnn : 0 ≤ k)
    (h : p * k ≤ (Real.sqrt 2) - 1) :
    1 - p * k ≥ (1 - p) ^ ((1 + p * k) * k) := by
  have gerber_bound :
      (1 - p) ^ ((1 + p * k) * k) ≤
        1 - p * (1 + p * k) * k + (p * (1 + p * k) * k) ^ 2 / 2 := by
    convert rpow_upper_bound_quadratic p ((1 + p * k) * k) hp0 hp1 (by positivity) using 1
    ring_nf
  have h_quad : (p * k) ^ 2 + 2 * (p * k) - 1 ≤ 0 := by
    nlinarith [show 0 ≤ p * k by positivity,
      Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
  nlinarith [mul_nonneg hp0 gnn]

end Util

section FiberCard

/-- The fiber cardinalities of a function partition the domain: `∑ b, |f⁻¹(b)| = |α|`.

This is the Fintype version of `Finset.card_eq_sum_card_fiberwise` over the full universe. -/
lemma sum_fiber_card {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) : ∑ b : β, Fintype.card {a : α | f a = b} = Fintype.card α := by
  simp_rw [Fintype.card_subtype, Set.mem_setOf_eq, Finset.card_filter]
  rw [Finset.sum_comm]
  simp [eq_comm]

end FiberCard
