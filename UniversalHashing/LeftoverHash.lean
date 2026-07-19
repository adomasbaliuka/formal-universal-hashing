/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import UniversalHashing.AlmostUniversal
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Rat.Star
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Leftover Hash Lemma

We state the **Classical Leftover Hash Lemma**
(Lemma 1 in Tomamichel–Schaffner–Smith–Renner, "Leftover Hashing Against Quantum Side
Information", arXiv:1002.2436).
TODO INCLUDE IN BIBLIOGRAPHY, FIX BIBLIOGRAPHY

## Classical Leftover Hash Lemma (Lemma 1)

**Setup.**  Let:
- `X` take values in a finite type `Input` and `E` in a finite type `SideInfo`,
  with joint distribution `μ : PMF (Input × SideInfo)`.
- `H : HashFamily Seed Input Output` be a δ-almost-universal₂ family
  (`H.almostUniversal2 δ`), with `Output` playing the role of `{0,1}^ℓ`
  (so `Fintype.card Output = 2^ℓ`).
- `f : Input → Output` be drawn *uniformly* from the family (i.e., by drawing
  `s : Seed` uniformly and setting `f = H s`).
- `Z := f(X)` be the extracted output.

**Claim.**  On average over the choice of `f`, the joint distribution of `(Z, E)` is
`Δ`-close to `Uniform(Output) ⊗ μ_E` in total-variation distance, where

  `Δ = (1/2) · √(|Output| · δ - 1 + |Output| · p_guess(X|E))`

and `p_guess(X|E)` is the **guessing probability** of `X` given `E`
(equal to `2^(-H_min(X|E))`, the inverse power of the classical conditional min-entropy).

## Definitions needed (classical)

The three new definitions below are the minimum required to *state* Lemma 1:

1. `guessingProb`     — the optimal guessing probability of `X` given classical side info `E`.
2. `avgTVDistFromUniform` — the total-variation distance of the hashed output from uniform,
                             averaged over the seed.
3. `classicalLeftoverHash` — the statement of Lemma 1 (currently `sorry`).

Note: `HashFamily.almostUniversal2` (δ-AU₂) is already defined in
`UniversalHashing.AlmostUniversal`.

## References

* Tomamichel, Schaffner, Smith, Renner (2010), arXiv:1002.2436.
-/

@[expose] public section


open scoped NNReal ENNReal

/-! ### Classical probability setup -/



section ClassicalLeftoverHash

variable {Input SideInfo Output Seed : Type*}
  [Fintype Input] [Fintype SideInfo] [Fintype Output] [Fintype Seed]
  [DecidableEq SideInfo] [DecidableEq Output]

/--
The **conditional guessing probability** of `X` given classical side information `E`,
with joint distribution `μ : PMF (Input × SideInfo)`.

Defined as:
  `p_guess(X|E) = ∑_e μ_E(e) · max_x μ_{X|E=e}(x)`

This equals `2^(-H_min(X|E))` where `H_min(X|E)` is the classical conditional min-entropy.
The guessing probability is a rational-valued, operationally meaningful quantity:
it is the success probability of the best strategy for guessing `X` given `E`.

In the special case with no side information (or deterministic `E`):
  `p_guess(X) = max_x μ_X(x) = 2^(-H_min(X))`.
-/
noncomputable def guessingProb (μ : PMF (Input × SideInfo)) : ℝ :=
  -- Marginal on SideInfo: μ_E(e) = ∑_x μ(x, e)
  -- Conditional: μ_{X|E=e}(x) = μ(x, e) / μ_E(e)
  -- p_guess = ∑_e μ_E(e) · max_x μ_{X|E=e}(x) = ∑_e max_x μ(x, e)
  ∑ e : SideInfo, (⨆ x : Input, (μ (x, e)).toReal)

/--
The **classical min-entropy** of `X` conditioned on `E` under joint distribution `μ`,
defined as the negative binary logarithm of the guessing probability:

  `H_min(X|E)_μ = -log₂(p_guess(X|E))`
-/
noncomputable def classicalCondMinEntropy (μ : PMF (Input × SideInfo)) : ℝ :=
  -Real.logb 2 (guessingProb μ)

/-- A probability distribution on a finite type, represented as a probability mass function.
    Each element is assigned a nonnegative real probability, and probabilities sum to 1. -/
structure ProbDist (α : Type*) where
  [instFintype : Fintype α]
  /-- The probability mass function -/
  pmf : α → ℚ
  /-- Probabilities are nonnegative -/
  nonneg : ∀ a, 0 ≤ pmf a
  /-- Probabilities sum to 1 -/
  sum_one : ∑ a, pmf a = 1

-- (An earlier `instance {α} (p : ProbDist α) : Fintype α := p.instFintype` was removed
-- when porting: `p` is explicit and cannot be synthesised, which Lean v4.32 rejects.
-- Every consumer below takes `[Fintype _]` explicitly, so it was redundant.)

def ProbDist.uniform (α : Type*) [Fintype α] [Inhabited α] : ProbDist α where
  pmf := fun _ ↦ 1 / Fintype.card α
  nonneg := by simp
  sum_one := by simp
def ProbDist.map {α β : Type*} [Fintype β] [DecidableEq β]
    (f : α → β) (p : ProbDist α)
    : ProbDist β where
  pmf := fun b ↦
    let : Fintype α := p.instFintype
    ∑ a : α, if b = f a then p.pmf a else 0
  nonneg := by
    intro b
    let : Fintype α := p.instFintype
    apply Fintype.sum_nonneg
    intro a
    simp only [Pi.zero_apply]
    split_ifs
    · exact p.nonneg a
    · rfl
  sum_one := by
    rw [Finset.sum_comm, ← p.sum_one]
    simp


open scoped BigOperators Set Order

/-- Note: measured in Nats -/
noncomputable def myMinEntropy (α : Type) [Fintype α]
    (p : ProbDist α) : ℝ :=
  - Real.log (⨆ a : α, p.pmf a)

/-! ### Total variation distance from uniform -/

/--
The **total-variation distance** between two distributions `μ ν`:

  `tvDist μ ν = (1/2) · ∑_a |μ(a) - ν(a)|`
-/
def tvDist {α : Type*} [Fintype α] (μ ν : ProbDist α) : ℚ :=
  (1 / 2) * ∑ a : α, |(μ.pmf a) - (ν.pmf a)|

/--
The total-variation distance of a distribution `μ : PMF Output` from the uniform
distribution over `Output`:

  `tvDistFromUniform μ = tvDist μ Uniform(Output)`
-/
def ProbDist.tvDistFromUniform {α : Type*} [Fintype α] [Inhabited α] (μ : ProbDist α) : ℚ :=
  tvDist μ (ProbDist.uniform α)

/--
When applying a hash function `f = H s` to a random variable `X ~ μ_X`, we get an output
distribution `μ_Z` over `Output`. This function computes the **pushforward** distribution
`Z = f(X)`.

The input distribution `μ_X : PMF Input` is given. The seed `s : Seed` determines `f`.
-/
noncomputable def hashOutputDist (μ_X : ProbDist Input) (H : HashFamily Seed Input Output)
    (s : Seed) : ProbDist Output :=
  μ_X.map (H s)

/--
The **average total-variation distance** from uniform of `Z = f(X)`,
where `f = H s` is drawn from the hash family by choosing `s` uniformly from `Seed`:

  `E_{s ∈ Seed}[tvDistFromUniform(Z_s)]`

This is the quantity that the Leftover Hash Lemma bounds.
-/
noncomputable def avgTVDistFromUniform [Nonempty Output] [Inhabited Output]
    (μ_X : ProbDist Input) (H : HashFamily Seed Input Output) : ℚ :=
  (∑ s : Seed, (hashOutputDist μ_X H s).tvDistFromUniform) / Fintype.card Seed

/-! ### The Classical Leftover Hash Lemma -/

/--
**Classical Leftover Hash Lemma** (Lemma 1 in arXiv:1002.2436, no side information case).

Let `μ_X : PMF Input` be a probability distribution over inputs,
and let `H : HashFamily Seed Input Output` be a `δ`-almost-universal₂ hash family
with output alphabet `Output` (of size `2^ℓ`).

Then, averaging over the uniform choice of seed `s : Seed`, the total-variation distance
of `Z = H s X` from the uniform distribution on `Output` is bounded by:

  `E_s[Δ(Z)] ≤ (1/2) · √(|Output| · δ + |Output| · p_guess(X) - 1)`

where `p_guess(X) = max_x μ_X(x)` is the guessing probability of `X`
(with no side information, `p_guess(X) = 2^(-H_min(X))`).

For a two-universal family (`δ = 1 / |Output|`), this gives the classical bound:
  `E_s[Δ(Z)] ≤ (1/2) · √(2^(ℓ - H_min(X)))`

**Note**: The full version with classical side information `E` requires additionally modeling
the joint distribution of `(X, E)` and the conditional distance; see `guessingProb` for
the conditional case. The quantum version (Lemma 2) requires quantum side information
and the definitions listed in the module header.
-/
theorem classicalLeftoverHash_noSideInfo
    [Nonempty Output] [Inhabited Output] [Nonempty Seed]
    (μ_X : ProbDist Input) (H : HashFamily Seed Input Output)
    (δ : ℚ) (hH : H.almostUniversal2 δ) :
    (avgTVDistFromUniform μ_X H : ℝ) ≤
      (1 / 2) * Real.sqrt (Fintype.card Output * δ + Fintype.card Output *
        (⨆ x : Input, ((μ_X.pmf x : ℚ) : ℝ)) - 1) := by
  sorry

end ClassicalLeftoverHash

end
