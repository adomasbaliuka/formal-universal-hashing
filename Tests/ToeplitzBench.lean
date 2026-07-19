/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import UniversalHashing.ToeplitzNTT

/-!
# Benchmark for the NTT-based Toeplitz hash

Times `toeplitzHashNTT` on pseudo-random inputs at several sizes, up to mapping
2·10⁶ input bits to 10⁶ output bits. Run with:

  lake exe toeplitzBench            -- everything
  lake exe toeplitzBench ntt        -- just the hash timings
  lake exe toeplitzBench core       -- just the raw NTT pipeline
  lake exe toeplitzBench schoolbook -- just the quadratic school-book baseline

Compiled calls to `toeplitzHashNTT` run `toeplitzHashNTTFast` via `@[csimp]`
(`toeplitzHashNTT_eq_fast`), so timing the two names is the same measurement; only
the public name is timed. This also serves as the regression guard on the `@[csimp]`
replacement: if it ever stopped firing, the largest size would revert to the quadratic
`BitVec` path and jump from a few seconds to several minutes.

This is a single-threaded measurement (the implementation is sequential). A digest of
each result is printed so the compiler cannot discard the computation.
-/

namespace ToeplitzBench

/-- xorshift64 PRNG step (quality is irrelevant here; speed and determinism matter). -/
def xorshift64 (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/--
Generate pseudo-random bits as a `Nat`, returning the advanced PRNG state.
Divide-and-conquer assembly keeps big-number concatenation `O(bits · log bits)`.
-/
partial def randNat (s : UInt64) (bits : ℕ) : Nat × UInt64 :=
  if bits = 0 then (0, s)
  else if bits ≤ 64 then
    let s' := xorshift64 s
    (s'.toNat % (1 <<< bits), s')
  else
    let half := bits / 2
    let (lo, s1) := randNat s half
    let (hi, s2) := randNat s1 (bits - half)
    (lo ||| (hi <<< half), s2)

/-- Time one `toeplitzHashNTT m n` evaluation on a pseudo-random seed and input. -/
def benchNTT (m n : ℕ) (seed : UInt64) : IO Unit := do
  let (pNat, s1) := randNat seed (m + n - 1)
  let (xNat, _) := randNat s1 n
  let param : BitVec (m + n - 1) := BitVec.ofNat _ pNat
  let x : BitVec n := BitVec.ofNat _ xNat
  let t0 ← IO.monoNanosNow
  let digest := (toeplitzHashNTT m n param x).toNat % 1000003
  -- Printing the digest here (between the timer reads) forces the computation to
  -- complete before `t1` is read; the compiler cannot sink it past a use.
  IO.print s!"toeplitzHashNTT: {n} bits -> {m} bits  (digest {digest})"
  let t1 ← IO.monoNanosNow
  IO.println s!"  time: {(t1 - t0) / 1000000} ms"

/-- Time the school-book `toeplitzHash m n` (quadratic) for comparison. -/
def benchSchoolbook (m n : ℕ) (seed : UInt64) : IO Unit := do
  let (pNat, s1) := randNat seed (m + n - 1)
  let (xNat, _) := randNat s1 n
  let param : BitVec (m + n - 1) := BitVec.ofNat _ pNat
  let x : BitVec n := BitVec.ofNat _ xNat
  let t0 ← IO.monoNanosNow
  let digest := (BitVec.ofFnLE fun i : Fin m ↦
    decide (toeplitzHash m n param.toZMod2Fun x.toZMod2Fun i = 1)).toNat % 1000003
  IO.print s!"toeplitzHash (school-book): {n} bits -> {m} bits  (digest {digest})"
  let t1 ← IO.monoNanosNow
  IO.println s!"  time: {(t1 - t0) / 1000000} ms"

/--
Time the core `Vector UInt32` NTT pipeline (root-table generation, forward and inverse
transform) in isolation, without the `BitVec`/`Nat` bit conversions that
`toeplitzHashNTT` performs around it.
-/
def benchNTTCore (logSize : ℕ) (seed : UInt64) : IO Unit := do
  let sz := 2 ^ logSize
  let v : Vector UInt32 sz := Vector.ofFn fun i ↦
    (xorshift64 (seed + UInt64.ofNat i.val)).toUInt32 % mod32
  IO.println s!"-- core NTT pipeline, size 2^{logSize} = {sz}"
  let t0 ← IO.monoNanosNow
  let roots := ensureRoots sz
  IO.print s!"   ensureRoots  (digest {roots.toArray.foldl (· + ·) 0})"
  let t1 ← IO.monoNanosNow
  IO.println s!"  time: {(t1 - t0) / 1000000} ms"
  let t2 ← IO.monoNanosNow
  let fwd := nttInplace v false roots
  IO.print s!"   forward NTT  (digest {fwd.toArray.foldl (· + ·) 0})"
  let t3 ← IO.monoNanosNow
  IO.println s!"  time: {(t3 - t2) / 1000000} ms"
  let t4 ← IO.monoNanosNow
  let inv := nttInplace fwd true roots
  IO.print s!"   inverse NTT  (digest {inv.toArray.foldl (· + ·) 0})"
  let t5 ← IO.monoNanosNow
  IO.println s!"  time: {(t5 - t4) / 1000000} ms"

end ToeplitzBench

open ToeplitzBench in
def main (args : List String) : IO Unit := do
  let which := args.headD "all"
  if which == "core" || which == "all" then
    IO.println "== Core NTT (no BitVec/Nat conversions) =="
    benchNTTCore 20 7
    benchNTTCore 22 7
    IO.println ""
  if which == "ntt" || which == "all" then
    IO.println "== NTT-based Toeplitz hash, n = 2m =="
    IO.println "-- (runs toeplitzHashNTTFast via @[csimp]; expect ~2.6 s at the largest size)"
    benchNTT 1000 2000 0xdeadbeef
    benchNTT 10000 20000 42
    benchNTT 100000 200000 42
    benchNTT 1000000 2000000 42
    IO.println ""
  if which == "schoolbook" || which == "all" then
    IO.println "== School-book comparison (small sizes only; it is quadratic) =="
    benchSchoolbook 1000 2000 42
    benchSchoolbook 2000 4000 42
