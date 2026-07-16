/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Batteries.Data.BitVec.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.UInt

import UniversalHashing.BinConvolution.ConvolutionHelpers.NextPow2Lemmas

/-! # Definitions for GF(2) circular convolution via NTT -/

/-- The NTT-friendly prime modulus `p = 3·2³⁰ + 1 = 3221225473`, as a `UInt64`.
Its `2³⁰`-smooth factor `p - 1 = 3·2³⁰` provides power-of-two roots of unity for the transform. -/
def mod64 : UInt64 := 3 * 2^30 + 1

/-- The same prime modulus `p = 3·2³⁰ + 1 = 3221225473` as `mod64`, but as a `UInt32`. -/
def mod32 : UInt32 := 3 * 2^30 + 1

/-- `5` is a primitive root of `(ZMod p)ˣ`, used to generate the NTT roots of unity. -/
def primRoot : UInt64 := 5

/-- Montgomery negated inverse `p' = -p⁻¹ mod 2³²` (`= 3221225471`), used by `montMul`. -/
def montPprime : UInt32 := 3221225471

/-- Montgomery `R² mod p` for radix `R = 2³²` (`= 1789569709`).
`montMul a montR2` puts `a` into Montgomery form. -/
def montR2 : UInt32 := 1789569709

/-- Montgomery `R mod p = 2³² mod p` (`= 1073741823`); the Montgomery representation of `1`. -/
def montR1 : UInt32 := 1073741823

section MontgomeryArithmetic

@[inline] def addMod32 (a b : UInt32) : UInt32 :=
  if a >= mod32 - b then a - (mod32 - b) else a + b

@[inline] def subMod32 (a b : UInt32) : UInt32 :=
  if a >= b then a - b else a - b + mod32

@[inline] def montMul (a b : UInt32) : UInt32 :=
  let T  : UInt64 := a.toUInt64 * b.toUInt64
  let m  : UInt32 := T.toUInt32 * montPprime
  let mp : UInt64 := m.toUInt64 * mod64
  let lo : UInt64 := T.toUInt32.toUInt64 + mp.toUInt32.toUInt64
  let u  : UInt64 := (T >>> 32) + (mp >>> 32) + (lo >>> 32)
  if u >= mod64 then (u - mod64).toUInt32 else u.toUInt32

@[inline] def toMont (a : UInt32) : UInt32 := montMul a montR2

/-- Fuel-based square-and-multiply accumulator for modular exponentiation: with `fuel` rounds
left it folds the remaining exponent bits `e` into the running result `r`, squaring base `b`
each round. Called by `powModU64` with `fuel = 64`, enough for any `UInt64` exponent. -/
def powModAuxU64 (mod_ : UInt64) : ℕ → UInt64 → UInt64 → UInt64 → UInt64
  | 0,   _, _, r => r
  | f+1, b, e, r =>
    if e == 0 then r
    else powModAuxU64 mod_ f (b * b % mod_) (e >>> 1) (if e &&& 1 != 0 then r * b % mod_ else r)

/-- `base ^ exp mod mod_`, computed by square-and-multiply via `powModAuxU64`. -/
def powModU64 (base exp mod_ : UInt64) : UInt64 :=
  powModAuxU64 mod_ 64 (base % mod_) exp 1

-- 1.3  montMul computes a·b·R⁻¹ mod p (Montgomery reduction).

/-- Iterated Montgomery multiplication: apply `montMul · wm` exactly `j` times to `seed`. -/
def montPow (seed wm : UInt32) : ℕ → UInt32
  | 0 => seed
  | j + 1 => montMul (montPow seed wm j) wm

end MontgomeryArithmetic

-- Fill v[halfLen+i+1 .. halfLen+i+k] by multiplying successive entries by wm.
-- Works directly on Vector; size is preserved in the type.
def rootsInner (wm : UInt32) (halfLen : ℕ) {n : ℕ} :
    (k i : ℕ) → Vector UInt32 n → Vector UInt32 n
  | 0,   _, v => v
  | k+1, i, v =>
    let src := halfLen + i
    let dst := src + 1
    let v' := if hs : src < n then
      if hd : dst < n then v.set dst (montMul (v.get ⟨src, hs⟩) wm) hd else v
    else v
    rootsInner wm halfLen k (i + 1) v'

/-
What `ensureRoots'` computes:

Each outer iteration handles one power-of-two length `len = 2^(k+1)` and writes
to the slot `[2^k, 2^(k+1))` of the vector:

  v[2^k + 0]  ← montR1          = w_len^0 · R   (planted directly)
  v[2^k + 1]  ← montMul prev wm = w_len^1 · R
  ...
  v[2^k + j]                     = w_len^j · R    (for j < 2^k)

where  w_len = primRoot ^ ((MOD−1) / 2^(k+1))  mod MOD6   is the principal 2^(k+1)-th root of unity
and    R = 2^32 mod mod64 = montR1                           is the Montgomery factor.

Different passes write to disjoint slots, so no pass overwrites another's results.
-/

/-- `roots[2^k + j] = w_{2^(k+1)}^j · R mod mod64`  (Montgomery domain) -/
def ensureRoots (n : ℕ) : Vector UInt32 n :=
  if hn0 : n = 0 then ⟨#[], by subst hn0; rfl⟩ else
  let rec outer (v : Vector UInt32 n) (len : UInt64) (hn : 0 < n) :
      Nat → Vector UInt32 n
    | 0   => v
    | f+1 =>
      if h_gt : len.toNat > n then v
      else
        let halfLen := len / 2
        let wm := toMont ((powModU64 primRoot ((mod64 - 1) / len) mod64).toUInt32)
        have h_rI : halfLen.toNat + 0 + (halfLen.toNat - 1) < n := by
          simp only [halfLen, UInt64.toNat_div, UInt64.toNat_ofNat]
          cases h : len.toNat / 2 <;> simp_all +arith +decide
          linarith [Nat.div_mul_le_self (len.toNat) 2,
                    show n ≥ len.toNat from h_gt]
        have h_half : halfLen.toNat < n := by omega
        let v' := v.set halfLen.toNat montR1 h_half
        outer (rootsInner wm halfLen.toNat (halfLen.toNat - 1) 0 v') (len <<< 1) hn f
  outer (Vector.replicate n 0) 2 (Nat.pos_of_ne_zero hn0) 64

/-- Compute next index in bit-reveral order ("add 1 in bit-reversed binary") -/
def bitRevNext : ℕ → ℕ → ℕ → ℕ
  | 0,    j, bit => j ^^^ bit
  | f+1,  j, bit =>
    if j &&& bit == 0 then j ^^^ bit
    else bitRevNext f (j ^^^ bit) (bit >>> 1)

def bitRevLoop {n : ℕ} :
    (k i : ℕ) → Vector UInt32 n → ℕ → Vector UInt32 n
  | 0,   _, v, _ => v
  | k+1, i, v, j =>
    let i' := i + 1
    let j' := bitRevNext 64 j (n / 2)
    let v' := if i' < j' then
      let vi := if h : i' < n then v.get ⟨i', h⟩ else 0
      let vj := if h : j' < n then v.get ⟨j', h⟩ else 0
      let v1 := if h : i' < n then v.set i' vj h else v
      if h : j' < n then v1.set j' vi h else v1
    else v
    bitRevLoop k (i + 1) v' j'

def radix2Pass {n : ℕ} :
    (k i : ℕ) → Vector UInt32 n → Vector UInt32 n
  | 0,   _, a => a
  | k+1, i, a =>
    let lo := 2 * i
    let hi := lo + 1
    let a' := if h1 : lo < n then
      if h2 : hi < n then
        let u := a.get ⟨lo, h1⟩
        let v := a.get ⟨hi, h2⟩
        (a.set lo (addMod32 u v) h1).set hi (subMod32 u v) h2
      else a
    else a
    radix2Pass k (i + 1) a'

/--
#  ── Radix-4 butterfly ────────────────────────────────────────────────────────
Two-stage DIF decomposition. Stage 1 applies the same twiddle `t1` to both
`aB` (at offset `s`) and `aD` (at offset `len + s`) — this is intentional:
in this grouping both elements occupy the "odd" slot of their respective
half-group and share the same first-stage twiddle. `t2` and `t3` are the
distinct second-stage twiddles applied after the first-stage ±-combine.
-/
@[inline] def butterfly4 {n : ℕ}
    (a : Vector UInt32 n) (inverse : Bool) (roots : Vector UInt32 n)
    (s len i2 j2 : ℕ) : Vector UInt32 n :=
  let t1 : UInt32 :=
    if !inverse then roots.getD (s + j2) 0
    else if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0
    else roots.getD s 0
  let t2 : UInt32 :=
    if !inverse then roots.getD (len + j2) 0
    else if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0
    else roots.getD len 0
  let t3 : UInt32 :=
    if !inverse then roots.getD (len + j2 + s) 0
    else mod32 - roots.getD (2 * len - j2 - s) 0
  let aA := if h : i2 + j2 < n then a.get ⟨i2 + j2, h⟩ else 0
  let aB :=
    let raw := if h : i2 + j2 + s < n then a.get ⟨i2 + j2 + s, h⟩ else 0
    montMul raw t1
  let aC := if h : i2 + len + j2 < n then a.get ⟨i2 + len + j2, h⟩ else 0
  let aD :=
    let raw := if h : i2 + len + j2 + s < n then a.get ⟨i2 + len + j2 + s, h⟩ else 0
    montMul raw t1
  let P := addMod32 aA aB
  let Q := subMod32 aA aB
  let R := addMod32 aC aD
  let S := subMod32 aC aD
  let t2R := montMul t2 R
  let t3S := montMul t3 S
  let a0 := if h : i2 + j2 < n
    then a.set (i2 + j2) (addMod32 P t2R) h else a
  let a1 := if h : i2 + len + j2 < n
    then a0.set (i2 + len + j2) (subMod32 P t2R) h else a0
  let a2 := if h : i2 + j2 + s < n
    then a1.set (i2 + j2 + s) (addMod32 Q t3S) h else a1
  if h : i2 + len + j2 + s < n
    then a2.set (i2 + len + j2 + s) (subMod32 Q t3S) h else a2

def radix4Inner {n : ℕ}
    (inverse : Bool) (roots : Vector UInt32 n) (s len i2 : ℕ) :
    Nat → Nat → Vector UInt32 n → Vector UInt32 n
  | 0,   _, a => a
  | k+1, j2, a =>
    radix4Inner inverse roots s len i2 k (j2 + 1)
      (butterfly4 a inverse roots s len i2 j2)

def radix4Middle {n : ℕ} (inverse : Bool) (roots : Vector UInt32 n) (s len : ℕ) :
    Nat → Nat → Vector UInt32 n → Vector UInt32 n
  | 0,   _, a => a
  | k+1, b, a =>
    let i2 := b * 2 * len
    radix4Middle inverse roots s len k (b + 1)
      (radix4Inner inverse roots s len i2 s 0 a)

def nttInplace {n : ℕ} (arr : Vector UInt32 n) (inverse : Bool)
    (roots : Vector UInt32 n) : Vector UInt32 n :=
  let a := if !inverse then arr.map toMont else arr
  let a : Vector UInt32 n := bitRevLoop (n - 1) 0 a 0
  let k : UInt64 :=
    let rec go : ℕ → ℕ → UInt64 → UInt64
      | 0,    _, k => k
      | f+1,  t, k => if t <= 1 then k else go f (t >>> 1) (k + 1)
    go 64 n 0
  let (a, start) :=
    if k &&& 1 != 0 then
      (radix2Pass (n / 2) 0 a, (4 : UInt64))
    else (a, (2 : UInt64))
  let a :=
    let rec outerLoop (a : Vector UInt32 n) (len : UInt64) : ℕ → Vector UInt32 n
      | 0   => a
      | f+1 =>
        if len.toNat * 2 > n then a else
          let s := len >>> 1
          outerLoop (radix4Middle inverse roots s.toNat len.toNat (n / (2 * len.toNat)) 0 a)
                    (len <<< 2) f
    outerLoop a start 64
  if inverse then
    let inv_n : UInt32 := (powModU64 n.toUInt64 (mod64 - 2) mod64).toUInt32
    a.map (fun x ↦ montMul x inv_n)
  else a

/--
GF(2) circular convolution: `(a * b)[i] = ⊕ₖ (a[k] ∧ b[(i−k) mod n])`.
Equivalently, multiplication in `GF(2)[X] / (Xⁿ − 1)`.
Computed via radix-4 NTT with Montgomery arithmetic.
Uses `2n`-point NTT to avoid aliasing; folds result[i] + result[i+n] to recover
the circular (period-n) convolution from the linear product.

This is only correct for `n < 2 ^ 29 ≈ 2.6e8`.
-/
def circularConvolutionGf2 {n : ℕ} (a b : BitVec n) : BitVec n :=
  -- Padding to have NTT size be a power of two.
  -- Using `2 * n` because we actually need linear convolution due to the padding
  let m : ℕ := Nat.nextPowerOfTwo (2 * n)
  have : 2 * n ≤ m := nextPow2_nat_ge (2 * n)
  let roots : Vector UInt32 m := ensureRoots m
  let fa : Vector UInt32 m := .ofFn fun i ↦
    if h : i.val < n then if a.getLsb ⟨i.val, h⟩ then 1 else 0 else 0
  let fb : Vector UInt32 m := .ofFn fun i ↦
    if h : i.val < n then if b.getLsb ⟨i.val, h⟩ then 1 else 0 else 0
  let fa : Vector UInt32 m := nttInplace fa false roots
  let fb : Vector UInt32 m := nttInplace fb false roots
  let prod_fafb : Vector UInt32 m := fa.zip fb |>.map (fun xy ↦ montMul xy.1 xy.2)
  let result : Vector UInt32 m := nttInplace prod_fafb true roots
  BitVec.ofFnLE fun i : Fin n ↦
    ((result.get ⟨i.val, by omega⟩ + result.get ⟨i.val + n, by omega⟩) &&& 1) == 1

/--
Specification of circular convolution on bit vectors.
Note that for `Bool`, summing is `xor`, while multiplication is `and`.
-/
def BitVec.circConvolutionBruteforce {n : ℕ} (v1 v2 : BitVec n) : BitVec n :=
  BitVec.ofFnLE fun i : Fin n ↦
    ∑ (j : Fin n), v1[j] * v2[i - j]


section Testing

set_option linter.hashCommand false

#guard 0b1111 == circularConvolutionGf2 (0b1100) (0b1010#4)
#guard 0b1111 == BitVec.circConvolutionBruteforce 0b1100 0b1010#4
#guard
  let a := 0b11000010010010#101
  let b := 0b01010101001001#101
  circularConvolutionGf2 a b == BitVec.circConvolutionBruteforce a b

end Testing
