/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

import UniversalHashing.Basic
import UniversalHashing.ToeplitzGeneral

/-!
This module defines a universal-2 hash by vector matrix multiplication with Toeplitz matrices.

Toeplitz matrices are defined in `ToeplitzGeneral.lean`.

Main result: `binToeplitz_mulVec_isUniversal2` shows that matrix-vector multiplication
with (binary) Toeplitz matrices is universal-2.
-/


open scoped Nat

/--
Main result:
Multiplication (mod p) by a random Toeplitz matrix is a universal-2 hash family.
-/
theorem toeplitzModp_mulVec_isUniversal2 (m n p : ℕ) [NeZero m] [NeZero n]
    [hp : Fact (Nat.Prime p)] :
    HashFamily.universal2
      (fun (M : ToeplitzMatrix m n (ZMod p)) (v : Fin n → ZMod p) ↦ M.val.mulVec v) := by
  intro v w hvw
  have hp_pos : 0 < p := hp.out.pos
  have h_card :
        (Finset.univ.filter
          (fun M : ToeplitzMatrix m n (ZMod p) ↦ M.val.mulVec (v - w) = 0)).card
        ≤ Fintype.card (ToeplitzMatrix m n (ZMod p)) / Fintype.card (Fin m → ZMod p) := by
    have : ∀ y : Fin m → ZMod p,
        (Finset.univ.filter
          (fun M : ToeplitzMatrix m n (ZMod p) ↦ M.val.mulVec (v - w) = y)).card
        = (Finset.univ.filter
          (fun M : ToeplitzMatrix m n (ZMod p) ↦ M.val.mulVec (v - w) = 0)).card
        := by
      intro y
      obtain ⟨M, hM⟩ := toeplitz_mulVec_surjective (sub_ne_zero_of_ne hvw) y
      rw [Finset.card_filter, Finset.card_filter]
      apply Finset.sum_bij (fun M' _ ↦ ⟨M'.val - M.val, toeplitzSub M' M⟩)
      · intros
        simp_all only [ne_eq, Finset.mem_univ]
      · simp only [Finset.mem_univ, forall_const]
        intro _ _ h
        apply Subtype.ext
        simpa using congr_arg Subtype.val h
      · intro b hb
        use ⟨b.val + M.val, by
          intro i i' j j' hij
          simp_all only [ne_eq, Matrix.IsToeplitz, Finset.mem_univ, Matrix.add_apply]
          apply congr_arg₂ (· + ·) (b.2 (by aesop)) (M.2 (by aesop))⟩
        aesop
      · simp_all [sub_eq_iff_eq_add, Matrix.sub_mulVec]
    have h_card :
        (Finset.univ : Finset (ToeplitzMatrix m n (ZMod p))).card
         = ∑ y : Fin m → ZMod p, (Finset.univ.filter (fun M : ToeplitzMatrix m n (ZMod p)
           ↦M.val.mulVec (v - w) = y)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_fiberwise]
    simp_all only [ne_eq, Finset.card_univ, Finset.sum_const, Fintype.card_pi, ZMod.card,
        Finset.prod_const, Fintype.card_fin, smul_eq_mul, Nat.pow_eq_zero, hp_pos.ne',
        false_and, not_false_eq_true, mul_div_cancel_left₀, le_refl]
  rw [Nat.le_div_iff_mul_le] at h_card <;> norm_num [Fintype.card_pi] at *
  · simp_all [Matrix.mulVec_sub, sub_eq_iff_eq_add, zero_add]
  · simp_all [pow_pos]

/-- Toeplitz hash, expressed using only bit vectors. -/
def toeplitzHash (m n : ℕ) :
    (HashFamily (Fin (m + n - 1) → ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2))
    := fun param v ↦
  (ToeplitzMatrix.from_params param).val.mulVec v

theorem toeplitzHash.universal2 (m n : ℕ) [NeZero m] [NeZero n] :
    (toeplitzHash m n).universal2 := by
  have bij : (ToeplitzMatrix.from_params (m:=m) (n:=n) (F:=ZMod 2)).Bijective :=
    ToeplitzMatrix.equiv_params.symm.bijective
  have : toeplitzHash m n
    = (fun (M : BinToeplitzMatrix m n) v ↦ M.val.mulVec v) ∘ ToeplitzMatrix.from_params := rfl
  have := (HashFamily.universal2_of_comp_bijective
    (fun (M : BinToeplitzMatrix m n) v ↦ M.val.mulVec v) bij)
  simp_all [toeplitzModp_mulVec_isUniversal2]

theorem Nat.ne_rat_ge1_of_lt1 (n : ℕ) (q : ℚ) (nne0 : n > 0) (qlt1 : q < 1) : n ≠ q := by aesop

/-- Counterexample: `toeplitzHash` is **NOT** in general strongly universal.
Proof by explicit computation, mapping two-bit vectors to 1-bit vectors.
-/
example : ¬ (toeplitzHash 2 1).stronglyUniversal2 := by
  simp only [toeplitzHash, HashFamily.stronglyUniversal2]
  push Not
  use 0, 1
  refine ⟨not_eq_of_beq_eq_false rfl, ?_⟩
  simp only [Nat.reduceAdd, Nat.add_one_sub_one, Fintype.card_pi, ZMod.card, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Nat.reducePow, Nat.cast_ofNat, ne_eq]
  norm_num
  use 0, 1
  refine Nat.ne_rat_ge1_of_lt1 ?_ (1/4) ?_ ?_
  · decide
  · norm_num
