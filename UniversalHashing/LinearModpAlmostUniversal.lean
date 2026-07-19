/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import UniversalHashing.AlmostUniversal
public import UniversalHashing.LinearModp
public import UniversalHashing.DeltaUniversal

/-!
# Carter–Wegman affine family is (1/(p−1))-almost-strongly-universal₂

The affine family `linearHashFamily p` — seeds `(a, b) ∈ (ZMod p)²` with `a ≠ 0`,
hashing as `h_{a,b}(x) = a·x + b mod p` — is `almostStronglyUniversal2 (1/(p−1))`.

## Proof sketch

For distinct `x ≠ y`, the system `a·x + b = c, a·y + b = d` has a **unique** solution
`(a, b) ∈ (ZMod p)²` (by field arithmetic: subtract to get `a = (c−d)/(x−y)`). Since
the family requires `a ≠ 0`, the count is at most 1. Combined with
`|LinearIndex p| = (p−1)·p`, this gives probability `≤ 1/((p−1)·p) = (1/(p−1)) / p`.

## Main results

* `linearHashFamily.card_linearIndex`: `|LinearIndex p| = (p − 1) · p`.
* `linearHashFamily.card_collision_le_one`: at most one seed causes `h(x) = c ∧ h(y) = d`.
* `linearHashFamily.almostStronglyUniversal2`: the family is `(1/(p−1))`-ASU₂.
* `linearHashFamily.almostUniversal2`: immediate corollary (0-AU, since `a ≠ 0` in a field).
-/

@[expose] public section


section LinearFamilyAlmostUniversal

variable {p : ℕ} [Fact p.Prime]

/-- `LinearIndex p` has cardinality `(p − 1) · p`.

The seed type `{(a, b) : (ZMod p)² | a ≠ 0}` bijects with
`{a : ZMod p | a ≠ 0} × ZMod p`, giving `(p − 1) · p`. -/
theorem linearHashFamily.card_linearIndex :
    Fintype.card (LinearIndex p) = (p - 1) * p := by
  convert Fintype.card_subtype _
  erw [Finset.card_filter, Finset.sum_product]
  simp +decide
  erw [Finset.sum_comm]
  simp +decide [Finset.sum_ite, Finset.filter_ne']
  ring


/-- For distinct inputs `x ≠ y`, at most one seed `(a, b)` with `a ≠ 0` satisfies
`a·x + b = c` and `a·y + b = d` simultaneously.

*Proof sketch*: subtracting gives `a·(x − y) = c − d`; since `x − y ≠ 0` in the field
`ZMod p`, `a` is uniquely determined, and then so is `b`. -/
theorem linearHashFamily.card_collision_le_one
    {x y : ZMod p} (hxy : x ≠ y) (c d : ZMod p) :
    Fintype.card
      {s : LinearIndex p // linearHashFamily p s x = c ∧ linearHashFamily p s y = d} ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  unfold linearHashFamily
  simp_all +decide
  grind

end LinearFamilyAlmostUniversal

/-- The Carter–Wegman affine family `h_{a,b}(x) = a·x + b mod p` (prime `p`,
seed `(a, b)` with `a ≠ 0`) is `(1/(p−1))`-almost-strongly-universal₂:

  `Pr_{(a,b) : a≠0}[a·x + b = c  ∧  a·y + b = d]  ≤  (1/(p−1)) / p`

for all distinct `x ≠ y` and all `c, d : ZMod p`.

The bound is tight: when `c ≠ d`, the unique solution has `a ≠ 0`, so the probability
equals exactly `1 / (p·(p−1))`. -/
theorem linearHashFamily.almostStronglyUniversal2 (p : ℕ) [Fact p.Prime] :
    HashFamily.almostStronglyUniversal2 ((1 : ℚ) / (p - 1)) (linearHashFamily p) := by
  intro x y hxy c d
  have h_prob :
      probUniform (fun s : LinearIndex p =>
        linearHashFamily p s x = c ∧ linearHashFamily p s y = d) ≤
      (1 : ℚ) / ((p - 1) * p) := by
    apply le_trans (div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (linearHashFamily.card_collision_le_one hxy c d)) (by positivity))
    rw [linearHashFamily.card_linearIndex]
    norm_num [Nat.cast_sub (show 1 ≤ p from Nat.Prime.pos Fact.out)]
  convert h_prob using 1
  norm_num [div_div]
  ring


/-- The Carter–Wegman affine family is `0`-almost-universal₂: distinct inputs
`x ≠ y` never collide, since `a·x + b = a·y + b` implies `a·(x−y) = 0`, but
`a ≠ 0` and `x − y ≠ 0` in the field `ZMod p`. -/
theorem linearHashFamily.almostUniversal2 (p : ℕ) [Fact p.Prime] :
    HashFamily.almostUniversal2 0 (linearHashFamily p) := by
  intros x y hxy
  have h_eq : ∀ s : LinearIndex p,
      linearHashFamily p s x = linearHashFamily p s y → False := by
    unfold linearHashFamily
    aesop
  unfold probUniform
  aesop


-- NOTE (porting, 2026-07-19): this file originally ended with a `sorry`'d
-- `linearHashFamily.almostDeltaUniversal2 (1/(p-1))`. It is omitted here because
-- `UniversalHashing.PaperStatements` already *proves* a theorem of exactly that name and
-- statement. Lean does not reject the duplicate: the later import silently wins, so
-- keeping it would have replaced a proven theorem with a `sorry` (verified via
-- `#print axioms`, which reported `sorryAx`).

end
