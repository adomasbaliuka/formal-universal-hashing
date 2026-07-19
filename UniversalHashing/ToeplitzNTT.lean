/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import UniversalHashing.Basic
public import UniversalHashing.Toeplitz
public import UniversalHashing.BinConvolution.ConvolutionDefs
public import UniversalHashing.BinConvolution.ConvolutionSolution
import Batteries.Data.BitVec.Lemmas

/-! # Toeplitz hashing via NTT-based binary circular convolution

Computing the Toeplitz hash `toeplitzHash` by school-book matrix-vector multiplication
takes time quadratic in the block size.
The Toeplitz structure allows an `O(N log N)` algorithm (
see, e.g., [hayashi_tsurumaru2016] Appendix B.).

- embed the `m × n` Toeplitz matrix `T` into a **circulant** matrix
`C_T` of size `L × L` with `L = m + n - 1`, zero-pad the input vector to length `L`,
- compute the circulant-vector product as a circular convolution via the NTT
(`circularConvolutionGf2`).
- the first `m` entries of the result are `T x`; discard the rest.


A circulant matrix is determined by its first column `c_C`; its product with a vector is
the circular convolution of `c_C` with that vector. Writing the Toeplitz matrix's first
column as `c_T` and its first row (excluding the corner) as `r_T`, the embedding is
`c_C = c_T ++ reverse r_T`.

In the parameter layout of `ToeplitzMatrix.from_params` (where `T i j = param (i + (n-1) - j)`)
we have `c_T i = param (n-1+i)` and `r_T j = param (n-2-j)`, so the reversal cancels and

  `c_C i = if i < m then param (n-1+i) else param (i-m)`.

Main definitions:
* `toeplitzCirculantColumn`: first column of the circulant embedding, from the seed.
* `toeplitzHashNTT`: the Toeplitz hash family computed via `circularConvolutionGf2`,
  with seeds/inputs/outputs represented as `BitVec`s. This is the definition to state
  theorems about; thanks to a `@[csimp]` replacement, *compiled* calls to it run the
  fast implementation `toeplitzHashNTTFast`.
* `toeplitzHashNTTFast`: the same computation with `O(N log N)` divide-and-conquer
  `BitVec` bit extraction/assembly instead of quadratic per-bit big-integer accesses.

Main results:
* `toeplitzHashNTT_eq_toeplitzHash`: on the domain where the NTT convolution is proven
  correct (`m + n - 1 < 2 ^ 29`), `toeplitzHashNTT` computes exactly `toeplitzHash`
  under the evident `BitVec` ↔ `Fin _ → ZMod 2` correspondence (`BitVec.toZMod2Fun`).
* `toeplitzHashNTTFast_eq`: the fast implementation equals `toeplitzHashNTT`,
  unconditionally, as functions.
* `toeplitzHashNTT_eq_fast` (`@[csimp]`): the bare-constant form of that equality,
  which instructs the compiler to run `toeplitzHashNTTFast` wherever compiled code
  calls `toeplitzHashNTT` — kernel-checked, unlike `@[implemented_by]`.

`Tests/ToeplitzNTT.lean` additionally checks `toeplitzHashNTT`
(running the fast implementation via the `@[csimp]` replacement)
against the school-book `toeplitzHash` for small matrices.
-/

@[expose] public section

/--
First column of the circulant matrix that the Toeplitz matrix with parameter vector
`param` (in the layout of `ToeplitzMatrix.from_params`) embeds into:
the Toeplitz matrix's first column followed by its reversed first row (sans corner).
-/
def toeplitzCirculantColumn (m n : ℕ) (param : BitVec (m + n - 1)) : BitVec (m + n - 1) :=
  BitVec.ofFnLE fun i : Fin (m + n - 1) ↦
    if h : i.val < m then param.getLsb ⟨n - 1 + i.val, by omega⟩
    else param.getLsb ⟨i.val - m, by omega⟩

/--
The Toeplitz hash family, computed via the NTT-based binary circular convolution
`circularConvolutionGf2`: embed the seed's Toeplitz matrix into a circulant
matrix (`toeplitzCirculantColumn`), zero-pad the input to length `m + n - 1`, convolve,
and keep the low `m` bits.

Bit `k` of the seed corresponds to `param k` in `toeplitzHash`; bits of input/output
correspond to vector entries, `1 : ZMod 2` ↔ `true`.

This is the reference definition, written for auditability and proofs. As written it has
quadratic `BitVec` boundary cost, but compiled code never pays it: a `@[csimp]`
replacement (`toeplitzHashNTT_eq_fast`) makes compiled calls run the equivalent
`O(N log N)` implementation `toeplitzHashNTTFast`.
-/
def toeplitzHashNTT (m n : ℕ) : HashFamily (BitVec (m + n - 1)) (BitVec n) (BitVec m) :=
  fun param x ↦
    (circularConvolutionGf2
      (toeplitzCirculantColumn m n param)
      (x.setWidth (m + n - 1))).setWidth m

/-! ## Correctness -/

/-- Decode a bit vector into a `ZMod 2` vector (LSB-first, `true ↦ 1`). -/
def BitVec.toZMod2Fun {w : ℕ} (v : BitVec w) : Fin w → ZMod 2 :=
  fun k ↦ if v.getLsb k then 1 else 0

/-- The ring homomorphism from `Bool` (with `xor` as `+` and `and` as `*`) to `ZMod 2`. -/
def boolToZMod2 : Bool →+* ZMod 2 where
  toFun b := if b then 1 else 0
  map_one' := rfl
  map_mul' := by decide
  map_zero' := rfl
  map_add' := by decide

/--
The key index computation of the circulant embedding: for an output index `i < m` and
an input index `k < n`, entry `i - k` (cyclically) of the circulant's first column is the
Toeplitz parameter `i + (n - 1) - k`, i.e. the matrix entry `T i k` in the layout of
`ToeplitzMatrix.from_params`.
-/
private lemma toeplitzCirculantColumn_getLsb_sub (m n : ℕ) [NeZero (m + n - 1)]
    (param : BitVec (m + n - 1)) (i k : Fin (m + n - 1))
    (hi : i.val < m) (hk : k.val < n) :
    (toeplitzCirculantColumn m n param).getLsb (i - k)
      = param.getLsb ⟨i.val + (n - 1) - k.val, by omega⟩ := by
  unfold toeplitzCirculantColumn
  rw [BitVec.getLsb_ofFnLE]
  have hL : (0:ℕ) < m + n - 1 := Nat.pos_of_ne_zero (NeZero.ne _)
  have hsub : (i - k).val = (i.val + ((m + n - 1) - k.val)) % (m + n - 1) := by
    simp [Fin.sub_def, Nat.add_comm]
  rcases Nat.lt_or_ge i.val k.val with hik | hki
  · -- `i - k` wraps around into the reversed-row part of the circulant column
    have hval : (i - k).val = (m + n - 1) + i.val - k.val := by
      rw [hsub, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [dif_neg (by omega : ¬ (i - k).val < m)]
    congr 1
    apply Fin.ext
    simp only [hval]
    omega
  · -- `i - k` lands in the Toeplitz-column part of the circulant column
    have hval : (i - k).val = i.val - k.val := by
      rw [hsub, ← Nat.add_sub_assoc (by omega), Nat.add_comm,
        Nat.add_sub_assoc (by omega), Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [dif_pos (by omega : (i - k).val < m)]
    congr 1
    apply Fin.ext
    simp only [hval]
    omega

/--
**Correctness of NTT-based Toeplitz hashing.** On the domain where the NTT convolution
is proven correct (`m + n - 1 < 2 ^ 29`), `toeplitzHashNTT` computes exactly the
school-book Toeplitz hash `toeplitzHash`, under the correspondence `BitVec.toZMod2Fun`
between bit vectors and `ZMod 2` vectors.
-/
theorem toeplitzHashNTT_eq_toeplitzHash (m n : ℕ) [NeZero m] [NeZero n]
    (hL : m + n - 1 < 2 ^ 29) (param : BitVec (m + n - 1)) (x : BitVec n) :
    BitVec.toZMod2Fun (toeplitzHashNTT m n param x)
      = toeplitzHash m n (BitVec.toZMod2Fun param) (BitVec.toZMod2Fun x) := by
  have hm := NeZero.ne m
  have hn := NeZero.ne n
  haveI : NeZero (m + n - 1) := ⟨by omega⟩
  funext i
  have hiL : i.val < m + n - 1 := by omega
  unfold toeplitzHashNTT
  rw [circular_convolution_gf2_correct _ _ hL]
  -- Reduce the LHS bit to the brute-force convolution sum in the `Bool` ring.
  change boolToZMod2 (((BitVec.circConvolutionBruteforce _ _).setWidth m).getLsb i)
    = toeplitzHash m n (BitVec.toZMod2Fun param) (BitVec.toZMod2Fun x) i
  have hbit : ((BitVec.circConvolutionBruteforce (toeplitzCirculantColumn m n param)
        (x.setWidth (m + n - 1))).setWidth m).getLsb i
      = ∑ j : Fin (m + n - 1),
          (toeplitzCirculantColumn m n param).getLsb j
            * (x.setWidth (m + n - 1)).getLsb (⟨i.val, hiL⟩ - j) := by
    simp only [BitVec.getLsb, BitVec.circConvolutionBruteforce]
    simp [i.isLt, hiL]
    rfl
  rw [hbit, map_sum]
  -- Reindex the sum by `j ↦ i - j`.
  rw [Fintype.sum_equiv (Equiv.subLeft (⟨i.val, hiL⟩ : Fin (m + n - 1)))
    _ (fun k ↦ boolToZMod2 ((toeplitzCirculantColumn m n param).getLsb
          ((⟨i.val, hiL⟩ : Fin (m + n - 1)) - k)
        * (x.setWidth (m + n - 1)).getLsb k)
      ) (fun k ↦ by rw [Equiv.subLeft_apply, sub_sub_cancel])]
  unfold toeplitzHash ToeplitzMatrix.from_params BitVec.toZMod2Fun
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  -- Common form of both sides: a sum over `ℕ` indices with vanishing terms beyond `n`.
  set G : ℕ → ZMod 2 := fun k ↦
    if hk : k < n then
      (if param.getLsb ⟨i.val + (n - 1) - k, by omega⟩ then (1 : ZMod 2) else 0)
        * (if x.getLsb ⟨k, hk⟩ then (1 : ZMod 2) else 0)
    else 0 with hG
  have hLHS : (∑ k : Fin (m + n - 1),
      boolToZMod2 ((toeplitzCirculantColumn m n param).getLsb
          ((⟨i.val, hiL⟩ : Fin (m + n - 1)) - k)
        * (x.setWidth (m + n - 1)).getLsb k))
      = ∑ k ∈ Finset.range (m + n - 1), G k := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : k.val < n
    · rw [hG, map_mul]
      simp only [dif_pos hk]
      rw [toeplitzCirculantColumn_getLsb_sub m n param ⟨i.val, hiL⟩ k i.isLt hk]
      congr 1
      have : (x.setWidth (m + n - 1)).getLsb k = x.getLsb ⟨k.val, hk⟩ := by
        simp [BitVec.getLsb, k.isLt]
      rw [this]
      rfl
    · have hxf : (x.setWidth (m + n - 1)).getLsb k = false := by
        change (BitVec.setWidth (m + n - 1) x).getLsbD k.val = false
        rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge x k.val (by omega), Bool.and_false]
      rw [hxf, show (false : Bool) = 0 from rfl, mul_zero, map_zero]
      simp only [hG, dif_neg hk]
  have hRHS : (∑ j : Fin n,
      (if param.getLsb ⟨i.val + (n - 1) - j.val, by omega⟩ then (1 : ZMod 2) else 0)
        * (if x.getLsb j then (1 : ZMod 2) else 0))
      = ∑ k ∈ Finset.range n, G k := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ ↦ by simp only [hG, dif_pos j.isLt, Fin.eta]
  rw [hLHS, hRHS]
  refine (Finset.sum_subset
    (fun k hk ↦ Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega))
    fun k _ hk ↦ ?_).symm
  simp only [hG]
  exact dif_neg (by simpa using hk)

/-! ## Fast implementation

`toeplitzHashNTT` is algorithmically `O(N log N)`, but its `BitVec` boundary work is
quadratic: every per-bit `getLsb`/`ofFnLE` access shifts the whole underlying big
integer. `toeplitzHashNTTFast` performs the same computation with divide-and-conquer
bit extraction and assembly (`O(N log N)` overall) and is proven **equal as a
function** to `toeplitzHashNTT` (`toeplitzHashNTTFast_eq`), so
`toeplitzHashNTT_eq_toeplitzHash` applies to it verbatim
(`toeplitzHashNTTFast_eq_toeplitzHash`).

The `@[csimp]` theorem `toeplitzHashNTT_eq_fast` then closes the loop: compiled code
that calls `toeplitzHashNTT` actually runs `toeplitzHashNTTFast`, so there is no slow
path at runtime and no reason to call the fast implementation by name.
-/

/--
Divide-and-conquer extraction of all bits of a `BitVec` (LSB first) in `O(w log w)`:
each level splits the vector with one whole-vector shift instead of shifting per bit.
-/
def BitVec.toBoolVector {w : ℕ} (v : BitVec w) : Vector Bool w :=
  if h : w ≤ 64 then
    Vector.ofFn fun i ↦ v.getLsb i
  else
    Vector.cast (by omega)
      ((v.setWidth (w / 2)).toBoolVector ++ ((v >>> (w / 2)).setWidth (w - w / 2)).toBoolVector)
  termination_by w
  decreasing_by all_goals omega

lemma BitVec.toBoolVector_getElem {w : ℕ} (v : BitVec w) (i : ℕ) (hi : i < w) :
    (BitVec.toBoolVector v)[i] = v.getLsbD i := by
  induction w using Nat.strong_induction_on generalizing i with
  | _ w ih =>
    unfold BitVec.toBoolVector
    split
    · simp [BitVec.getLsb, BitVec.getLsbD]
    · rename_i h
      rw [Vector.getElem_cast, Vector.getElem_append]
      split
      · rename_i hlt
        rw [ih (w / 2) (by omega) _ _ hlt, BitVec.getLsbD_setWidth]
        simp [hlt]
      · rename_i hge
        rw [ih (w - w / 2) (by omega) _ _ (by omega), BitVec.getLsbD_setWidth,
          BitVec.getLsbD_ushiftRight]
        simp [show i - w / 2 < w - w / 2 from by omega,
          Nat.add_sub_cancel' (by omega : w / 2 ≤ i)]

/--
Divide-and-conquer assembly of a `BitVec` from a bit function (LSB first) in
`O(w log w)`: each level concatenates two halves with one whole-vector shift instead
of inserting bits one at a time (as `BitVec.ofFnLE`'s `Nat.ofBits` does).
-/
def BitVec.ofBoolFnLE : (w : ℕ) → (Fin w → Bool) → BitVec w
  | w, f =>
    if h : w ≤ 64 then .ofFnLE f
    else
      (BitVec.ofBoolFnLE (w - w / 2) (fun i ↦ f ⟨w / 2 + i.val, by omega⟩) ++
       BitVec.ofBoolFnLE (w / 2) (fun i ↦ f ⟨i.val, by omega⟩)).cast (by omega)
  termination_by w _ => w
  decreasing_by all_goals omega

lemma BitVec.ofBoolFnLE_eq_ofFnLE (w : ℕ) (f : Fin w → Bool) :
    BitVec.ofBoolFnLE w f = BitVec.ofFnLE f := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    unfold BitVec.ofBoolFnLE
    split
    · rfl
    · rename_i h
      rw [ih (w - w / 2) (by omega), ih (w / 2) (by omega)]
      apply BitVec.eq_of_getLsbD_eq
      intro i hlt
      simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_ofFnLE]
      split
      · rename_i hlo
        rfl
      · rename_i hlo
        rw [dif_pos (by omega : i - w / 2 < w - w / 2)]
        congr 1
        exact Fin.ext (show w / 2 + (i - w / 2) = i by omega)

/--
Fast implementation of `toeplitzHashNTT`: the same circulant-embedding NTT convolution
pipeline, but with divide-and-conquer `BitVec` bit extraction/assembly instead of
per-bit big-integer accesses. Proven equal to `toeplitzHashNTT` in
`toeplitzHashNTTFast_eq`.
-/
def toeplitzHashNTTFast (m n : ℕ) : HashFamily (BitVec (m + n - 1)) (BitVec n) (BitVec m) :=
  fun param x ↦
    let sz : ℕ := Nat.nextPowerOfTwo (2 * (m + n - 1))
    have hsz : 2 * (m + n - 1) ≤ sz := nextPow2_nat_ge (2 * (m + n - 1))
    let roots : Vector UInt32 sz := ensureRoots sz
    let pBits : Vector Bool (m + n - 1) := param.toBoolVector
    let xBits : Vector Bool n := x.toBoolVector
    let fa : Vector UInt32 sz := .ofFn fun i ↦
      if h : i.val < m + n - 1 then
        if hm : i.val < m then
          (if pBits.get ⟨n - 1 + i.val, by omega⟩ then 1 else 0)
        else
          (if pBits.get ⟨i.val - m, by omega⟩ then 1 else 0)
      else 0
    let fb : Vector UInt32 sz := .ofFn fun i ↦
      if h : i.val < m + n - 1 then
        (if hn : i.val < n then (if xBits.get ⟨i.val, hn⟩ then 1 else 0) else 0)
      else 0
    let fa : Vector UInt32 sz := nttInplace fa false roots
    let fb : Vector UInt32 sz := nttInplace fb false roots
    let prod_fafb : Vector UInt32 sz := fa.zip fb |>.map (fun xy ↦ montMul xy.1 xy.2)
    let result : Vector UInt32 sz := nttInplace prod_fafb true roots
    (BitVec.ofBoolFnLE (m + n - 1) fun i : Fin (m + n - 1) ↦
      ((result.get ⟨i.val, by omega⟩
        + result.get ⟨i.val + (m + n - 1), by omega⟩) &&& 1) == 1).setWidth m

/-- The divide-and-conquer bit extraction agrees with `getLsb`. -/
lemma BitVec.toBoolVector_get_eq_getLsb {w : ℕ} (v : BitVec w) (i : Fin w) :
    v.toBoolVector.get i = v.getLsb i := by
  rw [Vector.get_eq_getElem, BitVec.toBoolVector_getElem _ _ i.isLt]
  rfl

/--
**The fast implementation is the reference implementation** — unconditionally, as an
equality of functions. Together with `toeplitzHashNTT_eq_toeplitzHash` this transfers
all correctness statements to `toeplitzHashNTTFast`.
-/
theorem toeplitzHashNTTFast_eq (m n : ℕ) :
    toeplitzHashNTTFast m n = toeplitzHashNTT m n := by
  funext param x
  -- The two `Vector.ofFn` inputs of the first forward NTT agree.
  have hfa : (Vector.ofFn (n := (2 * (m + n - 1)).nextPowerOfTwo) fun i ↦
      if h : i.val < m + n - 1 then
        if hm : i.val < m then
          (if param.toBoolVector.get ⟨n - 1 + i.val, by omega⟩ then (1 : UInt32) else 0)
        else
          (if param.toBoolVector.get ⟨i.val - m, by omega⟩ then (1 : UInt32) else 0)
      else 0)
      = Vector.ofFn fun i ↦
        if h : i.val < m + n - 1 then
          (if (toeplitzCirculantColumn m n param).getLsb ⟨i.val, h⟩ then (1 : UInt32) else 0)
        else 0 := by
    apply congrArg
    funext i
    simp only [BitVec.toBoolVector_get_eq_getLsb]
    by_cases h : i.val < m + n - 1
    · rw [dif_pos h, dif_pos h]
      unfold toeplitzCirculantColumn
      rw [BitVec.getLsb_ofFnLE]
      by_cases hm : i.val < m
      · rw [dif_pos hm, dif_pos hm]
      · rw [dif_neg hm, dif_neg hm]
    · rw [dif_neg h, dif_neg h]
  -- The two `Vector.ofFn` inputs of the second forward NTT agree.
  have hfb : (Vector.ofFn (n := (2 * (m + n - 1)).nextPowerOfTwo) fun i ↦
      if h : i.val < m + n - 1 then
        (if hn : i.val < n then (if x.toBoolVector.get ⟨i.val, hn⟩ then (1 : UInt32) else 0)
         else 0)
      else 0)
      = Vector.ofFn fun i ↦
        if h : i.val < m + n - 1 then
          (if (BitVec.setWidth (m + n - 1) x).getLsb ⟨i.val, h⟩ then (1 : UInt32) else 0)
        else 0 := by
    apply congrArg
    funext i
    simp only [BitVec.toBoolVector_get_eq_getLsb]
    by_cases h : i.val < m + n - 1
    · rw [dif_pos h, dif_pos h]
      by_cases hn : i.val < n
      · rw [dif_pos hn]
        have hbit : (BitVec.setWidth (m + n - 1) x).getLsb ⟨i.val, h⟩
            = x.getLsb ⟨i.val, hn⟩ := by
          change (BitVec.setWidth (m + n - 1) x).getLsbD i.val = x.getLsbD i.val
          rw [BitVec.getLsbD_setWidth]
          simp [h]
        rw [hbit]
      · rw [dif_neg hn]
        have hbit : (BitVec.setWidth (m + n - 1) x).getLsb ⟨i.val, h⟩ = false := by
          change (BitVec.setWidth (m + n - 1) x).getLsbD i.val = false
          rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge x i.val (by omega),
            Bool.and_false]
        rw [hbit]
        simp
    · rw [dif_neg h, dif_neg h]
  unfold toeplitzHashNTTFast toeplitzHashNTT circularConvolutionGf2
  simp only [BitVec.ofBoolFnLE_eq_ofFnLE, hfa, hfb]

/--
Compiler replacement (`@[csimp]`): compiled code that calls `toeplitzHashNTT` runs
`toeplitzHashNTTFast` instead. This is justified by the kernel-checked equality
`toeplitzHashNTTFast_eq` — proofs continue to see the reference definition, while
execution is `O(N log N)`.
-/
@[csimp]
theorem toeplitzHashNTT_eq_fast : @toeplitzHashNTT = @toeplitzHashNTTFast := by
  funext m n
  exact (toeplitzHashNTTFast_eq m n).symm

/--
Correctness of the fast NTT-based Toeplitz hash, transferred from
`toeplitzHashNTT_eq_toeplitzHash` via `toeplitzHashNTTFast_eq`.
-/
theorem toeplitzHashNTTFast_eq_toeplitzHash (m n : ℕ) [NeZero m] [NeZero n]
    (hL : m + n - 1 < 2 ^ 29) (param : BitVec (m + n - 1)) (x : BitVec n) :
    BitVec.toZMod2Fun (toeplitzHashNTTFast m n param x)
      = toeplitzHash m n (BitVec.toZMod2Fun param) (BitVec.toZMod2Fun x) := by
  rw [toeplitzHashNTTFast_eq]
  exact toeplitzHashNTT_eq_toeplitzHash m n hL param x

end
