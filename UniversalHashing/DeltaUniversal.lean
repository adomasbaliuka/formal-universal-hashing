/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import UniversalHashing.AlmostUniversal
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.Order.Star.Real
public import UniversalHashing.Basic

/-!
## ε-Almost Δ-Universal hashing

ε-almost-Δ-universal₂ (ε-A∆U₂), due to [BKST15, Definition 1.1], generalises ε-AU₂ by
bounding *all* difference probabilities, not just the zero-difference (collision) probability.
It requires `[AddCommGroup Output]` to express `H s x − H s y`.

Special cases of this definition are known by several names in the literature.
In particular, if `G` is the group of length-`l` strings of bits under element-wise XOR operation,
this case has been called
-"ε-otp secure" (e.g. Krawczyk94, 10.5555/1755009.1755041)
- ε-almost XOR universal (e.g. Rogaway99, Rogaway1999)

The chain of implications is:

  `almostStronglyUniversal2 ε` → `almostDeltaUniversal2 ε` → `almostUniversal2 ε`

The left implication sums the joint bound over all a : Output to bound each difference.
The right implication specialises b = 0 (since `H s x − H s y = 0 ↔ H s x = H s y`).

* `HashFamily.almostDeltaUniversal2 ε H` (defined in `UniversalHashing.Basic`):
  H is ε-A∆U₂ if for all distinct `x ≠ y` and
  every `b : Output`: `Pr_{s}[H s x − H s y = b] ≤ ε`. *[BKST15, Definition 1.1]*
* `HashFamily.almostDeltaUniversal2_mono`: ε-A∆U₂ is monotone in `ε`.
* `HashFamily.almostUniversal2_of_almostDeltaUniversal2`: A∆U₂ implies AU₂.
* `HashFamily.almostDeltaUniversal2_of_almostStronglyUniversal2`: ASU₂ implies A∆U₂.

-/

@[expose] public section

set_option relaxedAutoImplicit false
set_option autoImplicit false

section SeedInputOutputDeltaUniversal

variable {Seed Input Output : Type*}
  [Fintype Seed] [Fintype Output] [DecidableEq Output]
  [AddCommGroup Output]

/--
A perfectly Δ-universal family is `(1 / |Output|)`-A∆U₂ — with the optimal parameter,
since for fixed `x ≠ y` the probabilities `Pr[H s x − H s y = b]` sum to `1` over `b`.
-/
theorem HashFamily.almostDeltaUniversal2_of_deltaUniversal2
    (H : HashFamily Seed Input Output) (h : H.deltaUniversal2) :
    H.almostDeltaUniversal2 ((1 : ℚ) / Fintype.card Output) :=
  fun _ _ hxy b ↦ (h hxy b).le

omit [Fintype Output] in
/--
ε-A∆U₂ is monotone in `ε`: if `H` is `ε₁`-A∆U₂ and `ε₁ ≤ ε₂`, then `H` is `ε₂`-A∆U₂.
-/
theorem HashFamily.almostDeltaUniversal2_mono
    {ε₁ ε₂ : ℚ} (hε : ε₁ ≤ ε₂) (H : HashFamily Seed Input Output)
    (h : H.almostDeltaUniversal2 ε₁) : H.almostDeltaUniversal2 ε₂ :=
  fun x y hxy b ↦ (h hxy b).trans (by linarith)

omit [Fintype Output] in
/--
`almostDeltaUniversal2 ε` implies `almostUniversal2 ε`: specialise `b = 0`, since
`H s x − H s y = 0 ↔ H s x = H s y`.

*[BKST15, Definition 1.1, remark]*
-/
theorem HashFamily.almostUniversal2_of_almostDeltaUniversal2
    {ε : ℚ} (H : HashFamily Seed Input Output)
    (h : H.almostDeltaUniversal2 ε) : H.almostUniversal2 ε := by
  intro x y hxy; simpa [sub_eq_zero] using h hxy 0

/--
`almostStronglyUniversal2 ε` implies `almostDeltaUniversal2 ε`:
summing the joint bound `Pr[H s x = a ∧ H s y = a − b] ≤ ε / |Output|` over all `a`
gives `Pr[H s x − H s y = b] ≤ ε`.

This makes the full implication chain
`almostStronglyUniversal2 ε → almostDeltaUniversal2 ε → almostUniversal2 ε` explicit.

*[BKST15, Definition 1.1; implicit in the paper's discussion]*
-/
theorem HashFamily.almostDeltaUniversal2_of_almostStronglyUniversal2
    [Nonempty Seed]
    {ε : ℚ} (H : HashFamily Seed Input Output)
    (h : H.almostStronglyUniversal2 ε) : H.almostDeltaUniversal2 ε := by
  intro x y hxy b
  convert Finset.sum_le_sum fun a _ ↦ h hxy a (a - b) using 1
  any_goals exact Finset.univ
  · rfl
  · simp only [probUniform]
    rw [← Finset.sum_div, ← Nat.cast_sum]
    rw [← Fintype.card_sigma]
    refine congr_arg₂ _ (mod_cast Fintype.card_congr ?_) rfl
    exact ⟨fun ⟨i, hi⟩ ↦ ⟨H i x,
              ⟨i, by simp [sub_eq_iff_eq_add'.mp hi],
                  by simp [sub_eq_iff_eq_add'.mp hi]⟩⟩,
           fun ⟨a, ⟨i, hi₁, hi₂⟩⟩ ↦ ⟨i, by simp [hi₁, hi₂]⟩,
           fun ⟨i, hi⟩ ↦ by aesop,
           fun ⟨a, ⟨i, hi₁, hi₂⟩⟩ ↦ by aesop⟩
  · simp [div_eq_mul_inv, mul_left_comm]

/-- ε-A∆U₂ implies `(ε · |Output|)`-ASU₂: each joint probability
`Pr[H s x = a ∧ H s y = b]` equals `Pr[H s x − H s y = a − b]`
(same event after fixing one marginal), which is at most `ε` by A∆U₂.
The ASU₂ bound `(ε · |Output|) / |Output| = ε` then follows. -/
theorem HashFamily.almostStronglyUniversal2_of_almostDeltaUniversal2
    {ε : ℚ} (H : HashFamily Seed Input Output)
    (h : H.almostDeltaUniversal2 ε) :
    H.almostStronglyUniversal2 (ε * Fintype.card Output) := by
  intro x y hxy a b
  have hle : probUniform (fun s => H s x = a ∧ H s y = b) ≤
      probUniform (fun s => H s x - H s y = a - b) := by
    simp only [probUniform]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Fintype.card_le_of_injective
      (fun s : {i // H i x = a ∧ H i y = b} =>
        (⟨s.1, by have := s.2; rw [this.1, this.2]⟩ : {i // H i x - H i y = a - b}))
      (fun _ _ h => Subtype.ext (Subtype.mk.inj h))
  rw [show ε * Fintype.card Output / Fintype.card Output = ε from
      mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  exact hle.trans (h hxy (a - b))

end SeedInputOutputDeltaUniversal

end
