/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic


/-!
This module defines notions of universality for families of hash functions.

A **hash family** is a family of functions `Input → Output`.
Rather than define it as a set of functions, we put the choice of function into a type `Seed`.

## Universal-2

A function `hash : Seed → Input → Output` is Universal-2 if for any distinct inputs `x` and `y`,
the probability over a uniform random seed that `hash s x = hash s y` is at most `1 / |Output|`.

This is formalized as `(number of seeds causing collision) * |Output| ≤ |Seed|`.

We also give an alternative definition, proven equivalent, which the AIs seem to like more.
Let's see which we keep in the end...

## Strongly-universal-n

A family H is strongly universal (also known as "pairwise independent") if
  for all ``x ≠ y`` and all ``a b : Output``,
    ``\Pr_i [h_i(x) = a ∧ h_i(y) = b] = 1 / |Output|^2``

-/

@[expose] public section


/--
A **hash family** is a family of functions `Input → Output`.
Rather than define it as a set of functions, we put the choice of function into a type `Seed`.
-/
abbrev HashFamily (Seed Input Output : Type*) : Type _ :=
  Seed → Input → Output

section SeedInputOutput

-- In useful cases, these will *all* have instances `Fintype` and `DecidableEq`.
-- However, many theorems don't need those and I'd rather not use `omit` to silence linters.
variable {Seed Input Output : Type*}
  [Fintype Seed] [Fintype Output]
  [DecidableEq Output]

/--
A hash function taking a seed and an input is universal-2 if
for any distinct inputs x and y, the probability (over the seed) of a collision
is at most 1/|Output|.

This is expressed as: (number of seeds causing collision) * |Output| ≤ |Seed|.
-/
def HashFamily.universal2 (hash : HashFamily Seed Input Output) : Prop :=
  ∀ ⦃x y : Input⦄, x ≠ y →
    Fintype.card {s : Seed | hash s x = hash s y} * Fintype.card Output
    ≤ Fintype.card Seed

theorem HashFamily.universal2_of_seed_empty (hash : HashFamily Seed Input Output) [IsEmpty Seed] :
    hash.universal2 := by
  unfold HashFamily.universal2
  simp_all only [ne_eq, Set.coe_setOf, Fintype.card_eq_zero, zero_mul, le_refl, implies_true]

/-- The uniform probability of a predicate on `Seed`, modeled by counting. -/
def probUniform (p : Seed → Prop) [DecidablePred p] : ℚ :=
  (Fintype.card {i : Seed // p i} : ℚ) / (Fintype.card Seed : ℚ)

/-- Alternative (equivalent) statement of universal-2 using `probUniform`.

A family H is universal2 if for all distinct x ≠ y,
the collision probability is at most 1 / |Output|:

``Pr_i [h_i(x) = h_i(y)] ≤ 1 / |Output|``
-/
theorem HashFamily.universal2_iff_probUniform (H : HashFamily Seed Input Output) :
    H.universal2
    ↔
    ∀ ⦃x y : Input⦄, x ≠ y →
    probUniform (fun i ↦ H i x = H i y) ≤ (1 : ℚ) / (Fintype.card Output)
    := by
  simp only [ne_eq, probUniform, one_div]
  field_simp [mul_comm, mul_assoc, mul_left_comm]
  constructor <;> intro h x y hxy
  · have h_div : (Fintype.card {i : Seed // H i x = H i y}) * Fintype.card Output
        ≤ Fintype.card Seed := by
      exact_mod_cast h hxy
    by_cases hOutput : Fintype.card Output = 0 <;> by_cases hSeed : Fintype.card Seed = 0
    · simp_all
    · simp_all only [mul_zero, zero_le, Fintype.card_eq_zero_iff, not_isEmpty_iff,
      Fintype.card_eq_zero, CharP.cast_eq_zero, div_zero, ge_iff_le]
      exact False.elim <| hOutput.elim <| H hSeed.some x
    · simp_all
    · field_simp
      norm_cast
  · contrapose! h
    use x, y, hxy
    rw [div_lt_div_iff₀ ] <;> norm_cast <;> norm_num [Fintype.card_subtype ] at *
    · convert h using 1
    · exact Nat.pos_of_ne_zero ( by
      simp_all only [ne_eq]
      apply Aesop.BuiltinRules.not_intro
      intro a
      simp_all only [mul_zero, not_lt_zero] )
    · exact Fintype.card_pos_iff.mpr ⟨Classical.choose (Finset.card_pos.mp (by nlinarith))⟩

/--
A hash family is **strongly-universal-n** (also called "n-wise independent") if
- given `n` distinct inputs `a₁, a₂, ...`
- and n (not necessarily distinct) outputs `b₁, b₂, ...`,
exactly ``|HashFamily|/(|Output|^n)`` functions take `a₁` to `b₁` `a₂` to `b₂`, etc.

See [Wegman, Carter 1981](https://doi.org/10.1016/0022-0000(81)90033-7)
-/
def HashFamily.stronglyUniversal_n (n : ℕ) (H : HashFamily Seed Input Output) : Prop :=
  ∀ ⦃a : Fin n → Input⦄, a.Injective -- for n distinct Inputs `a₁, a₂, ...`
  →  ∀ (b : Fin n → Output), -- and n (not necessarily distinct) outputs `b₁, b₂, ...`,
  -- `|H|/(|B|^n)` functions take `a₁` to `b₁`, `a₂` to `b₂`, etc.
    Fintype.card {i : Seed // ∀ (j : Fin n), H i (a j) = b j }
      = (Fintype.card Seed : ℚ) / ((Fintype.card Output) ^ n : ℚ)

/--
Special case: a family H is **strongly-universal-2**
(also known as just "strongly universal", or "pairwise independent") if
  for all ``x ≠ y`` and all ``a b : Output``,
    ``\Pr_i [h_i(x) = a ∧ h_i(y) = b] = 1 / |Output|^2``.
-/
def HashFamily.stronglyUniversal2 (H : HashFamily Seed Input Output) : Prop :=
  ∀ ⦃x y : Input⦄, x ≠ y →
  ∀ a b : Output,
    Fintype.card {i : Seed // H i x = a ∧ H i y = b}
      = ((Fintype.card Seed) : ℚ) / (Fintype.card Output : ℚ)^2

/--
Equivalent statement of strongly-universal-2 using `probUniform`.

A family H is `stronglyUniversal2` if for all distinct x ≠ y, given two outputs a and b,
the probability to map `x ↦ a` and `y ↦ b` is exactly `1 / (|Output|^2)`.
-/
theorem HashFamily.stronglyUniversal2_iff_probUniform [Nonempty Seed]
    (H : HashFamily Seed Input Output) :
    H.stronglyUniversal2
    ↔
    ∀ ⦃x y : Input⦄, x ≠ y →
    ∀ a b : Output,
      probUniform (fun i ↦ H i x = a ∧ H i y = b)
        = 1 / ((Fintype.card Output : ℚ)^2) := by
  unfold HashFamily.stronglyUniversal2
  have : (Fintype.card Seed : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
    exact not_isEmpty_of_nonempty Seed
  constructor <;> intro h x y hxy a b <;> specialize h hxy a b
  · rw [probUniform, h]
    field_simp
  · rw [probUniform] at h
    field_simp at h
    exact h

/-- `stronglyUniversal2` is a special case of `strongly_universal_n` for `n = 2`. -/
theorem HashFamily.stronglyUniversal2_stronglyUniversal_n_2
    [Inhabited Seed] (H : HashFamily Seed Input Output) :
    H.stronglyUniversal2 ↔ H.stronglyUniversal_n 2 := by
  unfold stronglyUniversal2 stronglyUniversal_n
  have h : Fintype.card Seed ≠ 0 := by
    simp_all only [ne_eq, Fintype.card_ne_zero, not_false_eq_true]
  constructor
  · intro h a ainj b
    have : a 0 ≠ a 1 := by
      simp_all only [ne_eq, Fin.forall_fin_two, Fin.isValue, zero_ne_one, imp_false,
        not_false_eq_true, Function.Injective]
    have := h this (b 0) (b 1)
    field_simp at this
    convert this
    simp_all only [ne_eq, Fin.isValue, Fin.forall_fin_two]
  · intro h a b neq A B
    let as : Fin 2 → Input
    | 0 => a
    | 1 => b
    have : as.Injective := by
      unfold as Function.Injective
      grind only
    let Os : Fin 2 → Output
    | 0 => A
    | 1 => B
    have := h this Os
    field_simp
    convert this
    simp_all only [ne_eq, Fin.forall_fin_two, Fin.isValue, as, Os]

/-- `stronglyUniversal2` implies `universal2`. -/
theorem HashFamily.universal2_of_stronglyUniversal2
    (H : HashFamily Seed Input Output) :
    H.stronglyUniversal2 → H.universal2 := by
  intro h
  wlog seedNonempty : Fintype.card Seed ≠ 0
  · have : IsEmpty Seed := Fintype.card_eq_zero_iff.mp (Function.notMem_support.mp seedNonempty)
    exact HashFamily.universal2_of_seed_empty H
  convert (HashFamily.universal2_iff_probUniform H).mpr _
  intro x y hxy
  have : Nonempty Seed := Fintype.card_pos_iff.mp (Nat.zero_lt_of_ne_zero seedNonempty)
  have h_prob : ∀ a : Output,
    probUniform (fun i ↦ H i x = a ∧ H i y = a) = 1 / (Fintype.card Output : ℚ)^2 :=
      fun a ↦ H.stronglyUniversal2_iff_probUniform.mp h hxy a a
  have h_sum :
      probUniform (fun i ↦ H i x = H i y)
      = ∑ a : Output, probUniform (fun i ↦ H i x = a ∧ H i y = a) := by
    classical
    simp only [Fintype.card_subtype, probUniform]
    rw [← Finset.sum_div _ _ _, eq_comm]
    rw [← Nat.cast_sum, ← Finset.card_biUnion]
    · congr
      ext
      simp_all only [ne_eq, Fintype.card_ne_zero, not_false_eq_true, one_div, Finset.mem_biUnion,
        Finset.mem_univ, Finset.mem_filter, true_and, exists_eq_left']
      constructor <;> intros <;> simp_all only
    · intro a _ b _ hab
      exact Finset.disjoint_left.mpr fun i hi₁ hi₂ ↦ hab <| by aesop
  by_cases h : Fintype.card Output = 0 <;> simp_all [sq]

/--
If n is greater than the cardinality of the input space,
then any hash family is strongly universal-n (vacuously).
-/
theorem stronglyUniversal_n_of_gt_card [Fintype Input]
    (n : ℕ) (H : HashFamily Seed Input Output) (h : Fintype.card Input < n) :
    H.stronglyUniversal_n n := by
  intro a ha b
  exact absurd (Fintype.card_le_of_injective a ha) (by simpa using h)

/--
The composition of a universal2 function with an injective function is universal2.
-/
theorem HashFamily.universal2_of_comp_injective_seed (H : HashFamily Seed Input Output)
    {f : Seed → Seed} (hf : f.Injective) :
    H.universal2 ↔ HashFamily.universal2 (H ∘ f) :=  by
  constructor
  · intro h x y hxy
    convert h hxy using 1
    simp only [Function.comp_apply, Set.coe_setOf, Fintype.card_subtype, mul_eq_mul_right_iff]
    rw [Finset.card_filter, Finset.card_filter]
    exact Or.inl (Equiv.sum_comp (Equiv.ofBijective f
      ⟨hf, Finite.injective_iff_surjective.mp hf⟩) fun i ↦ if H i x = H i y then 1 else 0)
  · intro h x y hxy
    convert h hxy using 1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rw [Finset.card_filter, Finset.card_filter]
    rw [← Equiv.sum_comp (Equiv.ofBijective f ⟨hf, Finite.injective_iff_surjective.mp hf⟩)]
    simp_all only [Equiv.ofBijective_apply, Set.mem_setOf_eq, Function.comp_apply,
      mul_eq_mul_right_iff]
    exact Or.inl rfl

theorem HashFamily.universal2_of_comp_bijective {Seed2 : Type*} [Fintype Seed2]
    (H : HashFamily Seed Input Output)
    {f : Seed2 → Seed} (hf : f.Bijective) :
    H.universal2 ↔ HashFamily.universal2 (H ∘ f) := by
  have h_collision_count : ∀ x y : Input, x ≠ y
      → (Fintype.card {s : Seed2 | (H ∘ f) s x = (H ∘ f) s y})
      = (Fintype.card {s : Seed | H s x = H s y}) := by
    intro x y hxy
    exact Fintype.card_congr (Equiv.ofBijective (fun s ↦ ⟨f s, by aesop⟩) ⟨
        fun a b h ↦ by have := hf.1 (congrArg Subtype.val h) ; aesop,
        fun a ↦ by obtain ⟨s, hs⟩ := hf.2 a; aesop⟩)
  constructor <;> intro h x y hxy <;> have := h hxy
    <;> simp_all only [Multiset.bijective_iff_map_univ_eq_univ, ne_eq, Function.comp_apply,
      Set.coe_setOf, Fintype.card_subtype, not_false_eq_true, ge_iff_le]
    <;> replace hf := congr_arg Multiset.card hf
    <;> aesop

end SeedInputOutput

end
