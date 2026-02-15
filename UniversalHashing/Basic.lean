/-
This module defines notions of universality for families of hash functions.

## Universal-2

A function `hash : Seed → Input → Output` is Universal-2 if for any distinct inputs `x` and `y`,
the probability over a uniform random seed that `hash s x = hash s y` is at most `1 / |Output|`.

This is formalized as `(number of seeds causing collision) * |Output| ≤ |Seed|`.

We also give an alternative definition, proven equivalent, which the AIs seem to like more.
Let's see which we keep in the end...

## Strongly-universal-n

A family H is strongly universal (also known as ``pairwise independent'') if
  for all ``x ≠ y`` and all ``a b : Output``,
    ``\Pr_i [ h_i(x) = a ∧ h_i(y) = b ] = 1 / |Output|^2``

-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic


set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

variable {Seed Input Output : Type*}
  [Fintype Seed] [Fintype Input] [Fintype Output]
  [DecidableEq Seed] [DecidableEq Input] [DecidableEq Output]

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

TODO clean up proof. Partially AI-generated and way too long and cumbersome...
-/
example : IsUniversal2 (fun (s : Input → Output) (i : Input) => s i) := by
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
  rw [← pow_succ, Nat.sub_add_cancel ( Fintype.card_pos_iff.mpr ⟨ x ⟩ )]


/-- Abbreviation for the type of a family indexed by `Seed`, hashing `Input` to `Output`. -/
abbrev HashFamily (Seed Input Output : Type*) : Type _ := Seed → Input → Output

instance inst_Fintype_HashFamily [DecidableEq Seed] : Fintype (HashFamily Seed Input Output) :=
  ⟨Fintype.piFinset fun _ => Finset.univ, by simp⟩

/-- The uniform probability of a predicate on `Seed`, modeled by counting. -/
def probUniform (p : Seed → Prop) [DecidablePred p] : ℚ :=
  (Fintype.card {i : Seed // p i}) / (Fintype.card Seed)

/-
  Alternative (equivalent) definition of universal-2 using `probUniform`.

  (TODO let's see which we end up keeping)

  A family H is universal2 if for all distinct x ≠ y,
  the collision probability is at most 1 / |Output|:

    ``Pr_i [ h_i(x) = h_i(y) ] ≤ 1 / |Output|``
-/
def HashFamily.universal2 (H : HashFamily Seed Input Output) : Prop :=
  ∀ ⦃x y : Input⦄, x ≠ y →
    probUniform (fun i => H i x = H i y)
      ≤ (1 : ℚ) / (Fintype.card Output)

omit [DecidableEq Input] [Fintype Input] [DecidableEq Seed] in
/- The alternative definition is equilvalent to the older one. -/
theorem HashFamily.universal2_def_eq_old (H : HashFamily Seed Input Output) :
    IsUniversal2 H ↔ H.universal2 := by
  unfold HashFamily.universal2 IsUniversal2
  simp [probUniform]
  field_simp [mul_comm, mul_assoc, mul_left_comm]
  constructor <;> intro h x y hxy
  · have h_div : (Fintype.card {i : Seed // H i x = H i y}) * Fintype.card Output
        ≤ Fintype.card Seed := by
      convert h x y hxy using 1
      rw [Fintype.subtype_card ]
    by_cases hOutput : Fintype.card Output = 0
      <;> by_cases hSeed : Fintype.card Seed = 0 <;> simp_all
    · simp_all [Fintype.card_eq_zero_iff ]
      exact False.elim <| hOutput.elim <| H hSeed.some x
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
      simp_all only [mul_zero, not_lt_zero'] )
    · exact Fintype.card_pos_iff.mpr ⟨ Classical.choose ( Finset.card_pos.mp ( by nlinarith ) ) ⟩

/-
A family H is strongly universal (also known as ``pairwise independent'') if
  for all ``x ≠ y`` and all ``a b : Output``,
    ``\Pr_i [ h_i(x) = a ∧ h_i(y) = b ] = 1 / |Output|^2``.
-/
def HashFamily.stronglyUniversal (H : HashFamily Seed Input Output) : Prop :=
  ∀ ⦃x y : Input⦄, x ≠ y →
  ∀ a b : Output,
    probUniform (fun i => H i x = a ∧ H i y = b)
      = (1 : ℚ) / (Fintype.card Output : ℚ)^2

/-
A family H is strongly-universal-n (also called n-wise independent) if
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

omit [Fintype Input] [DecidableEq Seed] [DecidableEq Input] in
/- The definition `stronglyUniversal` is a special case of `strongly_universal_n` for `n = 2`. -/
lemma HashFamily.stronglyUniversal_of_stronglyUniversal_n
    [Inhabited Seed] (H : HashFamily Seed Input Output) :
    H.stronglyUniversal ↔ H.stronglyUniversal_n 2 := by
  unfold stronglyUniversal stronglyUniversal_n probUniform
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
    simp_all only [ne_eq, one_div, Fin.isValue, Fin.forall_fin_two]
  · intro h a b neq A B
    let as : Fin 2 → Input
    | 0 => a
    | 1 => b
    have : as.Injective := by
      unfold as Function.Injective
      intro _ _ ha
      simp_all only
      split at ha
      · split at ha
        · simp_all only [Fin.isValue]
        · simp_all only [ne_eq, Fintype.card_ne_zero, not_false_eq_true, Fin.forall_fin_two,
            Fin.isValue, not_true_eq_false]
      · split at ha
        · simp_all only [ne_eq, Fintype.card_ne_zero, not_false_eq_true, Fin.forall_fin_two,
            Fin.isValue, not_true_eq_false]
        · simp_all only [Fin.isValue]
    let Os : Fin 2 → Output
    | 0 => A
    | 1 => B
    have := h this Os
    field_simp
    convert this
    simp_all only [ne_eq, Fin.forall_fin_two, Fin.isValue, as, Os]

omit [DecidableEq Input] [Fintype Input] [DecidableEq Seed] in
/- Strongly-universal-2 implies universal-2.

Omitting unused instances to satisfy linter,
there will not be interesting cases where they are missing.
-/
theorem universal2_of_stronglyUniversal2 [DecidableEq Seed]
    (H : HashFamily Seed Input Output) :
    H.stronglyUniversal → H.universal2 := by
  intro h x y hxy
  have := h hxy
  simp_all only [ne_eq, one_div, ge_iff_le]
  have h_expand : (Nat.card {i : Seed // H i x = H i y})
        = ∑ a : Output, (Nat.card {i : Seed // H i x = a ∧ H i y = a}) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [← Finset.card_biUnion]
    congr
    · ext a
      simp_all only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        exists_eq_left']
      apply Iff.intro <;> intros <;> simp_all only
    · intro a _ b _ hab
      apply Finset.disjoint_left.mpr
      intros
      simp_all only [Finset.coe_univ, Set.mem_univ, ne_eq, Finset.mem_filter,
          Finset.mem_univ, true_and, and_self, and_false, not_false_eq_true]
  simp_all [Fintype.card_subtype, probUniform]
  simp_all [Finset.sum_div]
  by_cases h : Fintype.card Output = 0
  · simp_all only [CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    inv_zero, div_eq_zero_iff, Rat.natCast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    Finset.mem_univ, not_and, forall_const, mul_zero, le_refl]
  · simp_all only [sq, mul_inv_rev, ne_eq, Rat.natCast_eq_zero, not_false_eq_true,
    mul_inv_cancel_left₀, le_refl]
