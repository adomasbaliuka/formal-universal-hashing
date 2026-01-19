/-
This module defines Universal-2 hash functions.

A function `hash : Seed → Input → Output` is Universal-2 if for any distinct inputs `x` and `y`,
the probability over a uniform random seed that `hash s x = hash s y` is at most `1 / |Output|`.
This is formalized as `(number of seeds causing collision) * |Output| ≤ |Seed|`.
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

import UniversalHashing.Basic


/-
There are `2 ^ (n^2)` square binary matrices.
-/
lemma h_card_matrices (n : ℕ) : Fintype.card (Matrix (Fin n) (Fin n) (ZMod 2)) = 2 ^ (n ^ 2) := by
  simp only [Matrix, Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

/-
Binary Matrix-vector multiplication (using all matrices) is a Universal-2 hash function.
-/
lemma matrix_mulVec_isUniversal2 (n : ℕ) :
    IsUniversal2 (fun (M : Matrix (Fin n) (Fin n) (ZMod 2)) (v : Fin n → ZMod 2)
        => Matrix.mulVec M v) := by
  -- The condition $Mx = My$ is equivalent to $M(x-y) = 0$.
  -- Let $v = x-y$. Since $x \neq y$, $v \neq 0$.
  intro x y hxy
  set v := x - y with hv
  have hv_ne_zero : v ≠ 0 :=  sub_ne_zero_of_ne hxy
  -- We need to count the number of matrices $M$ such that $Mv = 0$.
  have h_count : (Finset.univ.filter (fun M : Matrix (Fin n) (Fin n) (ZMod 2)
        => M.mulVec v = 0)).card = (2 : ℕ) ^ (n ^ 2 - n) := by
    -- The linear map $M \mapsto Mv$ is surjective, so its kernel has cardinality $2^{n^2 - n}$.
    have h_surjective : Function.Surjective (fun M : Matrix (Fin n) (Fin n) (ZMod 2)
        => M.mulVec v) := by
      intro w
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv_ne_zero
      use Matrix.of (fun j k => if k = i then w j else 0)
      ext j
      simp  [Matrix.mulVec, dotProduct]
      cases Fin.exists_fin_two.mp ⟨v i, rfl⟩ <;> aesop
    -- The kernel of this map has dimension $n^2 - n$.
    have h_kernel1 : (Finset.univ.filter (fun M : Matrix (Fin n) (Fin n) (ZMod 2)
            => M.mulVec v = 0)).card * (Finset.univ : Finset (Fin n → ZMod 2)).card
            = (Finset.univ : Finset (Matrix (Fin n) (Fin n) (ZMod 2))).card := by
      have h_kernel2 : ∀ w : Fin n → ZMod 2,
            (Finset.univ.filter (fun M : Matrix (Fin n) (Fin n) (ZMod 2) => M.mulVec v = w)).card
            = (Finset.univ.filter (fun M : Matrix (Fin n) (Fin n) (ZMod 2) => M.mulVec v = 0)).card
            := by
        intro w
        obtain ⟨M₀, hM₀⟩ : ∃ M₀ : Matrix (Fin n) (Fin n) (ZMod 2), M₀.mulVec v = w := h_surjective w
        have h_preimage_card : Finset.filter (fun M : Matrix (Fin n) (Fin n) (ZMod 2)
                => M.mulVec v = w) Finset.univ = Finset.image (fun M => M₀ + M) (Finset.filter
                (fun M : Matrix (Fin n) (Fin n) (ZMod 2) => M.mulVec v = 0) Finset.univ) := by
          ext M; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.image_add_left,
            Finset.mem_preimage]
          simp only [← hM₀, Matrix.add_mulVec, Matrix.neg_mulVec]
          simp only [neg_add_eq_sub, sub_eq_zero]
        rw [h_preimage_card, Finset.card_image_of_injective _ ( add_right_injective M₀ )]
      have h_kernel3 : (Finset.univ : Finset (Matrix (Fin n) (Fin n) (ZMod 2))).card
            = ∑ w : Fin n → ZMod 2, (Finset.univ.filter (fun M : Matrix (Fin n) (Fin n) (ZMod 2)
            => M.mulVec v = w)).card := by
        simp  only [Finset.card_eq_sum_ones, Finset.sum_fiberwise]
      simp_all [mul_comm]
    simp_all [Finset.card_univ]
    apply mul_left_cancel₀ ( pow_ne_zero n two_ne_zero )
    rw [← pow_add, Nat.add_sub_of_le ( by nlinarith )]
    linarith [h_card_matrices n]
  have nat_pow_sub_mul_pow : (2 : ℕ) ^ (n ^ 2 - n) * 2 ^ n = 2 ^ (n ^ 2) := by
    apply pow_sub_mul_pow
    nlinarith
  simp_all [sub_eq_zero]
  convert (le_of_eq nat_pow_sub_mul_pow) using 2
  · convert h_count using 2 ; ext ; simp  [sub_eq_zero, Matrix.mulVec_sub]
  · simp  [Matrix, Fintype.card_pi]
    ring
