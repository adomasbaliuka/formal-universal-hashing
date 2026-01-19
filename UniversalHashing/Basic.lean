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


set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

variable {Seed Input Output : Type*} [Fintype Seed] [Fintype Input] [Fintype Output] 

open Classical in
/-
A hash function taking a seed and an input is universal-2 if
for any distinct inputs x and y, the probability (over the seed) of a collision
is at most 1/|Output|.
This is expressed as: (number of seeds causing collision) * |Output| <= |Seed|.
-/
def IsUniversal2 (hash : Seed → Input → Output) : Prop :=
  ∀ (x y : Input), x ≠ y →
    (Finset.univ.filter (fun s => hash s x = hash s y)).card * Fintype.card Output
    ≤ Fintype.card Seed

/-
The evaluation function `fun s i => s i` where the seed is a function `Input -> Output`
is a universal-2 hash function.
-/
example [DecidableEq Input] [DecidableEq Output] :
    IsUniversal2 (fun (s : Input → Output) (i : Input) => s i) := by
  intro x y hxy
  simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ]
  -- Let's count the number of functions $s : Input \to Output$ such that $s(x) = s(y)$.
  have h_count : (Finset.univ.filter (fun s : Input → Output => s x = s y)).card
                  ≤ Fintype.card Output ^ (Fintype.card Input - 1) := by
    have h_count : (Finset.univ.filter (fun s : Input → Output => s x = s y)).card
                    ≤ Finset.card (Finset.image (
                        fun s : Input → Output => fun i => if i = x then s y else s i)
                        (Finset.univ : Finset (Input → Output))) := by
      apply Finset.card_le_card
      intro s hs
      simp_all only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      use s
      ext x_1
      simp_all only [ite_eq_right_iff, implies_true]
    set im := Finset.image ( fun s : { i : Input // i ≠ x } → Output
            => fun i => if h : i = x then s ⟨y, by tauto ⟩ else s ⟨ i, by tauto⟩ ) Finset.univ
            with him
    refine le_trans h_count ( le_trans
        ( Finset.card_le_card (t:=im) <| Finset.image_subset_iff.mpr ?_a ) ?_bb )
    · simp only [Finset.mem_univ, him, ne_eq, Finset.mem_image, true_and, forall_const]
      exact fun s => ⟨fun i => s i, by aesop⟩
    · exact Finset.card_image_le.trans ( by simp only [ne_eq, Finset.card_univ, Fintype.card_pi,
      Finset.prod_const, Fintype.card_subtype_compl, Fintype.card_unique, le_refl] )
  convert Nat.mul_le_mul_right _ h_count using 1
  · convert rfl
  · rw [← pow_succ, Nat.sub_add_cancel ( Fintype.card_pos_iff.mpr ⟨ x ⟩ )]
