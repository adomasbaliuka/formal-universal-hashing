/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import UniversalHashing.AlmostUniversal
public import UniversalHashing.DeltaUniversal
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.LinearCombination

/-!
# Polynomial hash family

The **polynomial hash family** over a prime field `ZMod p` with degree bound `d` consists of all
polynomials of degree at most `d`, each identified by its coefficient tuple:

  `h_a(x) = a₀ + a₁·x + a₂·x² + ··· + aₐ·xᵈ  (mod p)`

where the seed `a : Fin (d+1) → ZMod p` encodes the coefficients and the input is an
evaluation point `x : ZMod p`.

This is a direct generalization of `linearHashFamily` (the `d = 1` case, which additionally
requires `a₁ ≠ 0`).

## Main results

* `polynomialHashFamily.stronglyUniversal_n`:
  The family is strongly-universal-`(d+1)`, i.e., `(d+1)`-wise independent.
  *Proof sketch*: For any `d+1` distinct inputs `x₀, …, xₐ` and any target outputs
  `b₀, …, bₐ`, the system `∑ᵢ aᵢ xⱼⁱ = bⱼ` is a Vandermonde system over the field `ZMod p`.
  Since the `xⱼ` are distinct and `p` is prime, the Vandermonde matrix is invertible, so
  there is exactly one solution — giving count `1 = p^(d+1) / p^(d+1)`.
  For `n ≤ d+1` distinct inputs and `n` outputs, the system is underdetermined with
  `d+1−n` free variables, giving `p^(d+1−n) = p^(d+1) / p^n` solutions, as required.

* `polynomialHashFamily.stronglyUniversal2`:
  Specialisation to `n = 2`: for `d ≥ 1` the family is pairwise independent.

* `polynomialHashFamily.almostUniversal2`:
  The family is `(1/p)`-AU₂ (collision probability at most `1/p`), which follows directly
  from `stronglyUniversal2`.

## Relation to other families

* `linearHashFamily`: the `d = 1` restriction to non-zero leading coefficient (a₁ ≠ 0);
  this is strictly smaller than `polynomialHashFamily p 1`.
* `mmhStar`: the `k`-dimensional inner product family (MMH\*) is *not* the same
  construction, though it achieves the same AU₂ bound.

## References

* [Carter, Wegman 1979] — original universal hashing paper.
* [Stinson 1994] — survey of universal hash families, [S94].
-/

@[expose] public section


section PolynomialHash

variable (p : ℕ) [Fact p.Prime] (d : ℕ)

/--
The **polynomial hash family** over `ZMod p` with degree bound `d`:

  `h_a(x) = ∑ i : Fin (d+1), a i * x ^ i  (mod p)`

- **Seed**: `a : Fin (d+1) → ZMod p` — the `d+1` polynomial coefficients (all choices, including
  zero leading coefficient)
- **Input**: `x : ZMod p` — the evaluation point
- **Output**: `ZMod p`

For `d = 0` this is the constant family; for `d = 1` with `a 1 ≠ 0` this recovers
`linearHashFamily`.
-/
def polynomialHashFamily :
    HashFamily (Fin (d + 1) → ZMod p) (ZMod p) (ZMod p) :=
  fun a x ↦ ∑ i : Fin (d + 1), a i * x ^ (i : ℕ)

/--
The polynomial hash family is **strongly-universal-`(d+1)`**, i.e., `(d+1)`-wise independent.

For any `d+1` distinct evaluation points `x₀, …, xₐ : ZMod p` and any target values
`b₀, …, bₐ : ZMod p`, exactly one seed `a : Fin (d+1) → ZMod p` satisfies
`h_a(xⱼ) = bⱼ` for all `j`. This is the Lagrange interpolation theorem over the field `ZMod p`:
a polynomial of degree `≤ d` is uniquely determined by its values at `d+1` distinct points.

More generally, for `n ≤ d+1` distinct inputs and `n` outputs, there are exactly
`p^(d+1−n)` satisfying seeds — exactly `|Seed| / |Output|^n`, as required.
-/
theorem polynomialHashFamily.stronglyUniversal_n :
    HashFamily.stronglyUniversal_n (d + 1) (polynomialHashFamily p d) := by
  intro pts hpts b
  -- Evaluating at all `d+1` nodes is additive and surjective.
  set f : (Fin (d + 1) → ZMod p) → (Fin (d + 1) → ZMod p) :=
    fun s j ↦ polynomialHashFamily p d s (pts j) with hf
  have hadd : ∀ s t, f (s + t) = f s + f t := by
    intro s t
    funext j
    simp only [hf, polynomialHashFamily, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [Pi.add_apply, add_mul]
  have hsurj : Function.Surjective f := by
    intro v
    -- Lagrange interpolation through the `d+1` distinct nodes.
    set q : Polynomial (ZMod p) := Lagrange.interpolate Finset.univ pts v with hq
    have hinj : Set.InjOn pts (Finset.univ : Finset (Fin (d + 1))) := fun a _ c _ h ↦ hpts h
    have hdeg : q.degree < (Finset.univ : Finset (Fin (d + 1))).card :=
      Lagrange.degree_interpolate_lt _ hinj
    have hnd : q.natDegree < d + 1 := by
      rcases eq_or_ne q 0 with h0 | h0
      · simp [h0]
      · have : q.degree < ((d + 1 : ℕ) : WithBot ℕ) := by simpa using hdeg
        exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr this
    refine ⟨fun i ↦ q.coeff i, ?_⟩
    funext j
    have heval : ∑ i : Fin (d + 1), q.coeff i * (pts j) ^ (i : ℕ) = q.eval (pts j) := by
      rw [Polynomial.eval_eq_sum_range' hnd, Finset.sum_range fun i ↦ q.coeff i * pts j ^ i]
    simp only [hf, polynomialHashFamily, heval]
    exact Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ j)
  have hprob := probUniform_eq_of_additive_surjective hadd hsurj b
  have hset : ∀ s : Fin (d + 1) → ZMod p,
      (f s = b) ↔ (∀ j, polynomialHashFamily p d s (pts j) = b j) :=
    fun s ↦ by simp [hf, funext_iff]
  have hSeed : (0 : ℚ) < Fintype.card (Fin (d + 1) → ZMod p) := by
    have : 0 < Fintype.card (Fin (d + 1) → ZMod p) := Fintype.card_pos
    exact_mod_cast this
  have hcardZ : (0 : ℚ) < Fintype.card (ZMod p) := by
    have : 0 < Fintype.card (ZMod p) := Fintype.card_pos
    exact_mod_cast this
  have hpow : ((Fintype.card (ZMod p) : ℚ)) ^ (d + 1) ≠ 0 := pow_ne_zero _ hcardZ.ne'
  rw [probUniform_congr hset, probUniform] at hprob
  have hcards : Fintype.card (Fin (d + 1) → ZMod p) = Fintype.card (ZMod p) ^ (d + 1) := by
    simp [Fintype.card_pi]
  rw [hcards] at hprob hSeed ⊢
  push_cast at hprob ⊢
  rw [div_self hpow]
  field_simp at hprob
  exact hprob

/-- Evaluating a single-coefficient seed. -/
private lemma sum_pi_single_mul (j : Fin (d + 1)) (v x : ZMod p) :
    ∑ i : Fin (d + 1), (Pi.single j v : Fin (d + 1) → ZMod p) i * x ^ (i : ℕ)
      = v * x ^ (j : ℕ) := by
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/--
The polynomial hash family is **strongly-universal-2** (pairwise independent) for `d ≥ 1`.

For any distinct `x ≠ y : ZMod p` and any targets `a b : ZMod p`, exactly
`p^(d-1)` seeds satisfy `h_s(x) = a ∧ h_s(y) = b`, giving probability `1/p²`.
-/
theorem polynomialHashFamily.stronglyUniversal2 (hd : 1 ≤ d) :
    (polynomialHashFamily p d).stronglyUniversal2 := by
  intro x y hxy a b
  -- Evaluating at the two points is an additive, surjective map onto `ZMod p × ZMod p`.
  set f : (Fin (d + 1) → ZMod p) → ZMod p × ZMod p :=
    fun s ↦ (polynomialHashFamily p d s x, polynomialHashFamily p d s y) with hf
  have hadd : ∀ s t, f (s + t) = f s + f t := by
    intro s t
    simp only [hf, polynomialHashFamily, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;>
      · rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by simp [Pi.add_apply, add_mul]
  have hsurj : Function.Surjective f := by
    rintro ⟨c₁, c₂⟩
    have hxy' : x - y ≠ 0 := sub_ne_zero_of_ne hxy
    set i₀ : Fin (d + 1) := ⟨0, by omega⟩ with hi₀
    set i₁ : Fin (d + 1) := ⟨1, by omega⟩ with hi₁
    set s₁ : ZMod p := (c₁ - c₂) / (x - y) with hs₁
    set s₀ : ZMod p := c₁ - s₁ * x with hs₀
    refine ⟨Pi.single i₀ s₀ + Pi.single i₁ s₁, ?_⟩
    have heval : ∀ z : ZMod p,
        polynomialHashFamily p d (Pi.single i₀ s₀ + Pi.single i₁ s₁) z = s₀ + s₁ * z := by
      intro z
      simp only [polynomialHashFamily, Pi.add_apply, add_mul]
      rw [Finset.sum_add_distrib, sum_pi_single_mul, sum_pi_single_mul]
      simp [hi₀, hi₁]
    have h₁ : s₀ + s₁ * x = c₁ := by
      rw [hs₀]; ring
    have h₂ : s₀ + s₁ * y = c₂ := by
      rw [hs₀, hs₁]
      field_simp
      ring
    simp only [hf, heval, h₁, h₂]
  have hprob := probUniform_eq_of_additive_surjective hadd hsurj (a, b)
  -- Translate the probability statement into the cardinality form.
  have hcard : Fintype.card (ZMod p × ZMod p) = Fintype.card (ZMod p) ^ 2 := by
    simp [Fintype.card_prod, sq]
  have hSeed : (0 : ℚ) < Fintype.card (Fin (d + 1) → ZMod p) := by
    have : 0 < Fintype.card (Fin (d + 1) → ZMod p) := Fintype.card_pos
    exact_mod_cast this
  have hset : ∀ s : Fin (d + 1) → ZMod p,
      (f s = (a, b)) ↔ (polynomialHashFamily p d s x = a ∧ polynomialHashFamily p d s y = b) :=
    fun s ↦ by simp [hf, Prod.ext_iff]
  have hcardZ : (0 : ℚ) < Fintype.card (ZMod p) := by
    have : 0 < Fintype.card (ZMod p) := Fintype.card_pos
    exact_mod_cast this
  have hsq : ((Fintype.card (ZMod p) : ℚ)) ^ 2 ≠ 0 := pow_ne_zero 2 hcardZ.ne'
  rw [probUniform_congr hset, probUniform, hcard] at hprob
  push_cast at hprob ⊢
  rw [div_eq_div_iff hSeed.ne' hsq] at hprob
  rw [eq_div_iff hsq]
  linear_combination hprob

/--
The polynomial hash family is **`(1/p)`-almost-universal₂**.

For distinct `x ≠ y`, the difference `h_a(x) − h_a(y)` is a non-zero polynomial of degree `≤ d`
in `a`, vanishing for exactly `p^d` of the `p^(d+1)` seeds, giving collision probability `1/p`.
This follows from `stronglyUniversal2`.
-/
theorem polynomialHashFamily.almostUniversal2 (hd : 1 ≤ d) :
    HashFamily.almostUniversal2 ((1 : ℚ) / p) (polynomialHashFamily p d) := by
  have h := HashFamily.almostUniversal2_of_almostStronglyUniversal2 _
    (HashFamily.almostStronglyUniversal2_of_stronglyUniversal2 _
      (polynomialHashFamily.stronglyUniversal2 p d hd))
  rwa [ZMod.card] at h

end PolynomialHash

end
