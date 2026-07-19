/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import UniversalHashing.AlmostUniversal
public import UniversalHashing.DeltaUniversal
public import UniversalHashing.PaperStatements

/-!
# Inner product hash family (MMH*)

The **inner product family** over a prime field `ZMod p` is defined by

  `h_x(m) = ∑ᵢ xᵢ · mᵢ  mod p`

where both seed `x` and input `m` are vectors in `(ZMod p)^k`.

This is the **MMH\*** family of Halevi–Krawczyk, cited in [BKST15, Theorem 1.3] as
`(1/p)`-Δ-universal. The seed is drawn uniformly from all of `Fin k → ZMod p`
(including `x = 0`), unlike `linearHashFamily` which excludes `a = 0`.

## Main results

* `mmhStar.almostUniversal2`:
  The family is `(1/p)`-AU₂.
  *Proof sketch*: for distinct `m ≠ m'`, find `i` with `mᵢ ≠ m'ᵢ`; then fixing all
  coordinates `xⱼ` (j ≠ i), exactly one value of `xᵢ` satisfies `∑ xⱼ(mⱼ−m'ⱼ) = 0`,
  giving `p^(k−1) / p^k = 1/p` collision probability.

* `mmhStar.almostDeltaUniversal2`:
  The family is `(1/p)`-A∆U₂.
  *Proof sketch*: `Pr[h_x(m) − h_x(m') = b] = Pr[h_x(m−m') = b]`, and by linearity
  each target is hit by exactly `p^(k−1)` seeds, giving probability `1/p`.

* `mmhStar.almostUniversal2_tight`:
  The bound `1/p` is tight: no smaller `ε` works for `k ≥ 1`.

## References

* [BKST15] Bibak, Kapron, Srinivasan, Tóth — *On an almost-universal hash function family
  with applications to authentication and secrecy codes*, §1.2, Theorem 1.3.
-/

@[expose] public section


section InnerProductHash

variable (p : ℕ) [Fact p.Prime] (k : ℕ)

-- The family itself is `mmhStar` from `UniversalHashing.PaperStatements`
-- (`fun x m ↦ ∑ i, m i * x i`). This file originally defined an identical family under
-- the name `innerProductHashFamily`; that duplicate was removed when porting.

/--
The inner product family is `(1/p)`-almost-Δ-universal₂.

Immediate from `mmhStar.deltaUniversal2`, which shows each difference value is attained
with probability *exactly* `1 / |ZMod p| = 1 / p`.

*[BKST15, Theorem 1.3 (Δ-universal bound)]*
-/
theorem mmhStar.almostDeltaUniversal2 :
    HashFamily.almostDeltaUniversal2 ((1 : ℚ) / p) (mmhStar p k) := by
  have h := HashFamily.almostDeltaUniversal2_of_deltaUniversal2 (mmhStar p k)
    (mmhStar.deltaUniversal2 p k)
  rwa [ZMod.card] at h

/--
The inner product family is `(1/p)`-almost-universal₂.

Immediate from `mmhStar.almostDeltaUniversal2`: a collision is the `b = 0` case of the
difference bound.

*[BKST15, Theorem 1.3 (AU bound)]*
-/
theorem mmhStar.almostUniversal2 :
    HashFamily.almostUniversal2 ((1 : ℚ) / p) (mmhStar p k) :=
  HashFamily.almostUniversal2_of_almostDeltaUniversal2 _ (mmhStar.almostDeltaUniversal2 p k)

/--
For `k = 0`, the family is trivially `0`-AU₂: the only input is the empty vector,
so there are no distinct pairs.
-/
theorem mmhStar.almostUniversal2_zero :
    HashFamily.almostUniversal2 0 (mmhStar p 0) := by
  intro x y hxy
  exact False.elim <| hxy <| by ext i; fin_cases i

/--
The bound `1/p` is tight for `k ≥ 1`: the family is not `ε`-AU₂ for any
`ε < 1/p`, specifically not for `ε = 1/p - 1/p^k`.

*Proof*: the zero vector `x = 0` collides with the unit vector `eᵢ` since
`h₀(m) = 0 = h_{eᵢ}(0)` for the input `m = 0`. Counting shows exactly
`p^(k−1)` seeds satisfy the collision condition for any two distinct inputs,
giving probability exactly `1/p`, which exceeds `1/p - 1/p^k`.
-/
theorem mmhStar.almostUniversal2_tight [NeZero k] :
    ¬ HashFamily.almostUniversal2 ((1 : ℚ) / p - 1 / p ^ k) (mmhStar p k) := by
  intro h
  have hp : 1 < p := Fact.out
  have hppos : (0 : ℚ) < p := by exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p)
  -- Any two distinct inputs will do; take `e₀` and `0`.
  set i₀ : Fin k := ⟨0, NeZero.pos k⟩ with hi₀
  set x : Fin k → ZMod p := fun i ↦ if i = i₀ then 1 else 0 with hx
  have hxy : x ≠ (fun _ ↦ 0) := by
    intro hc
    have h1 : (1 : ZMod p) = 0 := by simpa [hx] using congrFun hc i₀
    exact one_ne_zero h1
  -- `deltaUniversal2` pins the collision probability at exactly `1 / p`.
  have hexact : probUniform (fun s ↦ mmhStar p k s x = mmhStar p k s (fun _ ↦ 0))
      = 1 / p := by
    have hd := mmhStar.deltaUniversal2 p k hxy 0
    rw [ZMod.card] at hd
    simpa [sub_eq_zero] using hd
  have hle := h hxy
  rw [hexact] at hle
  have hpk : (0 : ℚ) < (p : ℚ) ^ k := pow_pos hppos k
  have : (0 : ℚ) < 1 / (p : ℚ) ^ k := by positivity
  linarith

/--
The bound `1/p` is tight for A∆U₂: the family is not `ε`-A∆U₂ for any `ε < 1/p`,
specifically not for `ε = 1/p - 1/p^k`.

Since `Pr[h_x(m) − h_x(m') = b] = 1/p` exactly for every `b` and every distinct
`m ≠ m'` (by the same counting argument as `almostDeltaUniversal2`), the A∆U₂ bound
is achieved with equality and cannot be improved.

*[BKST15, Theorem 1.3 (tightness)]*
-/
theorem mmhStar.almostDeltaUniversal2_tight [NeZero k] :
    ¬ HashFamily.almostDeltaUniversal2 ((1 : ℚ) / p - 1 / p ^ k) (mmhStar p k) := by
  intro h
  exact mmhStar.almostUniversal2_tight p k
    (HashFamily.almostUniversal2_of_almostDeltaUniversal2 _ h)

end InnerProductHash

end
