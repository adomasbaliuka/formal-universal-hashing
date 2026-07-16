/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Plausible

open Plausible

instance Vector.shrinkable {α} [Shrinkable α] {n : Nat} : Shrinkable (Vector α n) where
  shrink v :=
    (List.finRange n).flatMap fun i =>
      (Shrinkable.shrink (v.get i)).map (v.set i.val ·)

instance Vector.Arbitrary {n : Nat} {α} [Arbitrary α] : Arbitrary (Vector α n) where
  arbitrary := Vector.ofFnM fun _ => Arbitrary.arbitrary

instance Fin.shrinkableNat {n : Nat} : Shrinkable (Fin n) where
  shrink m := (Nat.shrink m.val).filterMap fun k =>
    if h : k < n then some ⟨k, h⟩ else none

instance Fin.arbitraryNat {n : Nat} : Arbitrary (Fin n) where
  arbitrary := do
    if h : 0 < n then
      let m ← Gen.choose Nat 0 (min (← Gen.getSize) (n - 1)) (Nat.zero_le _)
      return ⟨m, by omega⟩
    else
      throw (GenError.genError "Fin 0 has no elements")

