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

/-- `probUniform` respects pointwise-equivalent predicates. -/
theorem probUniform_congr {p q : Seed → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ s, p s ↔ q s) : probUniform p = probUniform q := by
  unfold probUniform
  rw [Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) h)]

/--
Fibers of an additive surjection between finite additive groups are equiprobable:
each value is hit with probability exactly `1 / |Output|`.

This is the counting core behind perfect Δ-universality of linear hash families
(all fibers are cosets of the kernel, hence equinumerous).
-/
theorem probUniform_eq_of_additive_surjective {Seed Output : Type*}
    [Fintype Seed] [Fintype Output] [DecidableEq Output]
    [AddCommGroup Seed] [AddCommGroup Output]
    {f : Seed → Output} (hadd : ∀ s t, f (s + t) = f s + f t)
    (hsurj : Function.Surjective f) (b : Output) :
    probUniform (fun s ↦ f s = b) = 1 / Fintype.card Output := by
  have hzero : f 0 = 0 := by simpa using (hadd 0 0).symm
  have hsub : ∀ s t, f (s - t) = f s - f t := fun s t ↦ by
    have h := hadd (s - t) t
    rw [sub_add_cancel] at h
    exact eq_sub_of_add_eq h.symm
  -- Every fiber is a translate of the kernel fiber, hence of the same size.
  have hfib : ∀ c : Output,
      Fintype.card {s : Seed // f s = c} = Fintype.card {s : Seed // f s = 0} := by
    intro c
    obtain ⟨s₀, hs₀⟩ := hsurj c
    exact Fintype.card_congr
      { toFun := fun s ↦ ⟨s.val - s₀, by rw [hsub, s.prop, hs₀, sub_self]⟩
        invFun := fun s ↦ ⟨s.val + s₀, by rw [hadd, s.prop, hs₀, zero_add]⟩
        left_inv := fun s ↦ Subtype.ext (by simp)
        right_inv := fun s ↦ Subtype.ext (by simp) }
  -- The fibers partition the seed space.
  have hsum : ∑ c : Output, Fintype.card {s : Seed // f s = c} = Fintype.card Seed :=
    Fintype.card_sigma.symm.trans <| Fintype.card_congr
      ⟨fun p ↦ p.2.val, fun s ↦ ⟨f s, s, rfl⟩,
       fun p ↦ by obtain ⟨c, s, rfl⟩ := p; rfl, fun s ↦ rfl⟩
  have hker : Fintype.card Seed
      = Fintype.card Output * Fintype.card {s : Seed // f s = 0} := by
    rw [← hsum, Finset.sum_congr rfl fun c _ ↦ hfib c, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
  have hker_pos : 0 < Fintype.card {s : Seed // f s = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨0, hzero⟩⟩
  have hK : (0 : ℚ) < Fintype.card Output := by
    have : 0 < Fintype.card Output := Fintype.card_pos_iff.mpr ⟨f 0⟩
    exact_mod_cast this
  have hkerQ : (0 : ℚ) < Fintype.card {s : Seed // f s = 0} := by exact_mod_cast hker_pos
  rw [probUniform, hfib b, hker]
  push_cast
  rw [div_eq_div_iff (by positivity) hK.ne']
  ring

/-- `probUniform` is invariant under reindexing the seed space by an equivalence. -/
theorem probUniform_comp_equiv {Seed2 : Type*} [Fintype Seed2]
    (e : Seed2 ≃ Seed) (p : Seed → Prop) [DecidablePred p] :
    probUniform (fun s ↦ p (e s)) = probUniform p := by
  unfold probUniform
  rw [Fintype.card_congr (e.subtypeEquiv fun _ ↦ Iff.rfl), Fintype.card_congr e]

/-- The probability of an event on a product seed space factors over the first coordinate:
`Pr_{s₁×s₂}[P] = (∑ s₁, Pr_{s₂}[P s₁]) / |S₁|`. -/
lemma probUniform_prod {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    (P : S₁ → S₂ → Prop) [∀ s₁ s₂, Decidable (P s₁ s₂)] :
    (Fintype.card {s : S₁ × S₂ // P s.1 s.2} : ℚ) / Fintype.card (S₁ × S₂) =
    (∑ s₁ : S₁, (Fintype.card {s₂ : S₂ // P s₁ s₂} : ℚ) / Fintype.card S₂) /
    Fintype.card S₁ := by
  simp only [Fintype.card_subtype, Fintype.card_prod, Nat.cast_mul, Finset.sum_div]
  rw [Finset.card_filter]
  erw [Finset.sum_product]
  simp [div_eq_mul_inv, mul_comm, Finset.mul_sum, mul_left_comm]

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

See [wegman_carter1981]
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

/-! ### ε-almost universality

Relaxations of `HashFamily.universal2` and `HashFamily.stronglyUniversal2` where
equality/bounds are replaced by a parameter `ε`. Theorems about these notions live in
`UniversalHashing.AlmostUniversal` and `UniversalHashing.DeltaUniversal`.
-/

/--
A hash family is **ε-almost-universal₂ (ε-AU₂)** with parameter `ε : ℚ` if for any two
distinct inputs `x` and `y`, the probability over a uniform random seed of a collision is
at most `ε`:

  `Pr_{s}[H s x = H s y] ≤ ε`

`HashFamily.universal2` is the special case `ε = 1 / |Output|`; see
`HashFamily.universal2_iff_probUniform`.

*Definition 1.1 in* [bibak_kapron_srinivasan_toth2015].
-/
def HashFamily.almostUniversal2 (ε : ℚ) (H : HashFamily Seed Input Output) : Prop :=
  ∀ ⦃x y : Input⦄, x ≠ y →
    probUniform (fun s ↦ H s x = H s y) ≤ ε

/--
A hash family is **ε-almost-strongly-universal₂ (ε-ASU₂)** with parameter `ε : ℚ` if
for every pair of distinct inputs `x ≠ y` and all outputs `a, b`:

  `Pr_{s}[H s x = a ∧ H s y = b] ≤ ε / |Output|`

`HashFamily.stronglyUniversal2` is the special case `ε = 1 / |Output|` where the bound is tight;
see `HashFamily.stronglyUniversal2_iff_almostStronglyUniversal2`.

*Definition 1.1 in* [bibak_kapron_srinivasan_toth2015]. This is the prevalent
definition in modern literature.

### Relationship to alternative definitions

[stinson1994] additionally requires **uniformity** `Pr_{s}[H s x = a] = 1 / |Output|`
(see `HashFamily.uniform`), i.e., the conjunction `H.uniform ∧ H.almostStronglyUniversal2 ε`.

The uniformity condition is motivated by Wegman–Carter MACs, where it ensures that
observing a tag `(m, t)` reveals no information about the key.
The two definitions coincide when `ε = 1 / |Output|` (the strongly-universal case):
the joint bound then forces all marginals to equal `1 / |Output|`, implying uniformity.
-/
def HashFamily.almostStronglyUniversal2 (ε : ℚ) (H : HashFamily Seed Input Output) : Prop :=
  ∀ ⦃x y : Input⦄, x ≠ y → ∀ (a b : Output),
    probUniform (fun s ↦ H s x = a ∧ H s y = b) ≤ ε / Fintype.card Output

/--
A hash family is **uniform** if every input maps to every output with equal probability:

  `Pr_{s}[H s x = a] = 1 / |Output|`

[stinson1994] defines ε-ASU₂ as the conjunction
`H.uniform ∧ H.almostStronglyUniversal2 ε`; see `HashFamily.almostStronglyUniversal2` for
a discussion of the two definitions and when they coincide.
-/
def HashFamily.uniform (H : HashFamily Seed Input Output) : Prop :=
  ∀ (x : Input) (a : Output),
    probUniform (fun s ↦ H s x = a) = (1 : ℚ) / Fintype.card Output

/--
A hash family is **ε-almost-Δ-universal₂ (ε-A∆U₂)** with parameter `ε : ℚ` if for any
two distinct inputs `x` and `y` and every group element `b : Output`:

  `Pr_{s}[H s x − H s y = b] ≤ ε`

This is strictly stronger than `almostUniversal2` (which only bounds the b = 0 case)
and strictly weaker than `almostStronglyUniversal2` (which bounds joint probabilities).

*Definition 1.1 in* [bibak_kapron_srinivasan_toth2015].

When `Seed = Fin ℓ → ZMod 2`, `Input = Fin m → ZMod 2`, `Output = Fin n → ZMod 2`, this is
equivalent to Krawczyk's ε-otp-security (Definition 1 in [krawczyk1995]) with **uniform** key
distribution: for any distinct M ≠ M' and any target b,
`Pr_{k uniform}[H(k, M') − H(k, M) = b] ≤ ε`.
-/
def HashFamily.almostDeltaUniversal2 [AddCommGroup Output]
    (ε : ℚ) (H : HashFamily Seed Input Output) : Prop :=
  ∀ ⦃x y : Input⦄, x ≠ y → ∀ (b : Output),
    probUniform (fun s ↦ H s x - H s y = b) ≤ ε

/--
A hash family is **Δ-universal₂ (perfectly Δ-universal)** if for any two distinct
inputs `x` and `y`, every difference value is attained with exactly the uniform
probability:

  `Pr_{s}[H s x − H s y = b] = 1 / |Output|`

This is `almostDeltaUniversal2` with the smallest possible parameter `ε = 1 / |Output|`,
attained with equality (see `HashFamily.almostDeltaUniversal2_of_deltaUniversal2`;
no smaller `ε` is possible for any family, since for fixed `x ≠ y` the probabilities
sum to `1` over `b : Output`).

Over the group `Fin n → ZMod 2` (bit strings under XOR) this property is commonly
called **XOR-universality**.
-/
def HashFamily.deltaUniversal2 [AddCommGroup Output]
    (H : HashFamily Seed Input Output) : Prop :=
  ∀ ⦃x y : Input⦄, x ≠ y → ∀ (b : Output),
    probUniform (fun s ↦ H s x - H s y = b) = (1 : ℚ) / Fintype.card Output

/--
A hash family is **additive** (Krawczyk's "⊕-linear" over bit strings) if every member
is an additive map: `H s (x + y) = H s x + H s y`.

*Definition 2 in* [krawczyk1994].
-/
def HashFamily.additive [Add Input] [Add Output]
    (H : HashFamily Seed Input Output) : Prop :=
  ∀ (s : Seed) (x y : Input), H s (x + y) = H s x + H s y

/--
A hash family is **ε-balanced** if no nonzero input concentrates on any output value:

  `Pr_{s}[H s x = c] ≤ ε` for all `x ≠ 0` and all `c`.

For `additive` families this is equivalent to `almostDeltaUniversal2 ε`
(`HashFamily.additive_balanced_iff_almostDeltaUniversal2`).

*Definition 3 in* [krawczyk1994].
-/
def HashFamily.balanced [Zero Input] (ε : ℚ) (H : HashFamily Seed Input Output) : Prop :=
  ∀ ⦃x : Input⦄, x ≠ 0 → ∀ (c : Output),
    probUniform (fun s ↦ H s x = c) ≤ ε

/--
A hash family is **ε-almost collision-flat universal₂ (ε-ACFU₂)** if it is uniform and
no *specific* collision value is hit too often:

  `Pr_{s}[H s x = a ∧ H s y = a] ≤ ε / |Output|` for all `x ≠ y` and all `a`.

Sits strictly between ε-ASU₂ (with uniformity) and ε-AU₂; see [Wiese, Boche 2024,
Lemma 1.2] (`ε-Almost Collision-Flat Universal Hash Functions and Mosaics of Designs`).
-/
def HashFamily.almostCollisionFlatUniversal2 (ε : ℚ)
    (H : HashFamily Seed Input Output) : Prop :=
  H.uniform ∧ ∀ ⦃x y : Input⦄, x ≠ y → ∀ (a : Output),
    probUniform (fun s ↦ H s x = a ∧ H s y = a) ≤ ε / Fintype.card Output

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
