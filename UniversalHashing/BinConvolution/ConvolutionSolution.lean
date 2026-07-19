/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import UniversalHashing.BinConvolution.ConvolutionHelpers.ConvolutionProof


/-! # Correctness of GF(2) circular convolution via NTT -/

@[expose] public section

theorem circular_convolution_gf2_correct {n : ℕ} (a b : BitVec n) (hn : n < 2 ^ 29) :
    circularConvolutionGf2 a b = BitVec.circConvolutionBruteforce a b := by
  apply circular_convolution_gf2_correct'
  · -- n < mod32.toNat = 3221225473 > 2^29
    have : mod32.toNat = 3221225473 := rfl
    omega
  · -- (Nat.nextPowerOfTwo (2 * n)) ∣ mod64.toNat - 1
    exact pow2_divides_MOD_sub_one n hn

end
