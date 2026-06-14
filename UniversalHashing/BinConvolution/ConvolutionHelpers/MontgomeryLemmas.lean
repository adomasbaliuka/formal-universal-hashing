/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Batteries.Data.BitVec.Lemmas
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import PrimeCert.Pocklington3
import PrimeCert.PowMod
import PrimeCert.SmallPrimes
import UniversalHashing.BinConvolution.ConvolutionDefs

/-!
# Constants
-/
section NTT_Constants


theorem MOD32_bound : mod32.toNat = 3221225473 := by decide

theorem MOD32_lt_two32 : mod32.toNat < 2 ^ 32 := by decide

theorem prime_3221225473 : Nat.Prime 3221225473 := prime_cert%
  [small {3},
   pock3 (3221225473, 5, 1, 0, 2 ^ 30 * 3)]

theorem mod32_eq_mod : mod64.toNat = mod32.toNat := by decide

theorem prime_mod : mod64.toNat.Prime := prime_3221225473

theorem MOD_eq : mod64.toNat = (3 * 2^30 + 1) := by decide

-- Montgomery arithmetic with R = 2^32 and modulus p = mod64.
-- montR1   = R     mod p   (Montgomery representation of 1)
theorem MONT_R1_spec : montR1.toNat = 2 ^ 32 % mod64.toNat := by decide

-- montR2   = R²    mod p   (conversion factor: montMul a montR2 = a·R mod p)
theorem MONT_R2_spec : montR2.toNat = 2 ^ 64 % mod64.toNat := by decide

-- montPprime satisfies p · p' ≡ −1 (mod R)  (used in Montgomery reduction)
theorem MONT_PPRIME_spec : (mod64.toNat * montPprime.toNat + 1) % 2 ^ 32 = 0 := by decide

-- montR1 ≡ 2^32 in ZMod p (used frequently to cancel the Montgomery factor)
theorem MONT_R1_ZMod : (montR1.toNat : ZMod mod32.toNat) = 2 ^ 32 := by
  have h : montR1.toNat = 2 ^ 32 % mod32.toNat :=
    MONT_R1_spec.trans (mod32_eq_mod ▸ rfl)
  rw [h, show (2 : ZMod mod32.toNat) ^ 32 = ((2 ^ 32 : ℕ) : ZMod mod32.toNat) from by
    norm_cast, ZMod.natCast_eq_natCast_iff]
  decide

theorem PRIM_ROOT_pow_ZMod : (primRoot.toNat : ZMod mod64.toNat) ^ (mod64.toNat - 1) = 1 := by
  exact @ZMod.pow_card_sub_one_eq_one _ (Fact.mk prime_mod) _ (by decide)

-- Bridge: (a : ZMod p)^e = ((powMod a e p : ℕ) : ZMod p), proved without evaluating a^e.
-- Uses PrimeCert's powMod (ℕ-based). Allows substituting concrete literal values before
-- using prove_pow_mod (which uses eagerReduce to avoid kernel deep recursion).
private lemma zmod_cast_pow_eq_powMod_cast (a e p : ℕ) :
    (a : ZMod p) ^ e = ((powMod a e p : ℕ) : ZMod p) := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_natCast_iff]
  simp [Nat.ModEq, powMod, Nat.mod_mod_of_dvd]

private lemma prim_root_pow_div3_ne_one :
    (primRoot.toNat : ZMod mod64.toNat) ^ ((mod64.toNat - 1) / 3) ≠ 1 := by
  rw [zmod_cast_pow_eq_powMod_cast]
  rw [(by decide : primRoot.toNat = 5),
      (by decide : mod64.toNat = 3221225473),
      (by decide : (3221225473 - 1) / 3 = 1073741824)]
  rw [(by prove_pow_mod : powMod 5 1073741824 3221225473 = 1610563584)]
  decide

/-- `primRoot^{(mod64-1)/2} = -1` in `ZMod mod32.toNat`. -/
lemma prim_root_half_eq_neg_one :
    (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2) = -1 := by
  rw [zmod_cast_pow_eq_powMod_cast]
  rw [(by decide : primRoot.toNat = 5),
      (by decide : mod32.toNat = 3221225473),
      (by decide : mod64.toNat = 3221225473),
      (by decide : (3221225473 - 1) / 2 = 1610612736)]
  rw [(by prove_pow_mod : powMod 5 1610612736 3221225473 = 3221225472)]
  decide

private lemma prim_root_pow_div2_ne_one :
    (primRoot.toNat : ZMod mod64.toNat) ^ ((mod64.toNat - 1) / 2) ≠ 1 := by
  have h : (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2) ≠ 1 :=
    fun heq => absurd (prim_root_half_eq_neg_one.symm.trans heq) (by decide)
  exact mod32_eq_mod.symm ▸ h

theorem prim_root_PRIM_ROOT :
    IsPrimitiveRoot (primRoot.toNat : ZMod mod64.toNat) (mod64.toNat - 1) := by
  refine ⟨PRIM_ROOT_pow_ZMod, ?_⟩
  intro l hl
  -- Strategy: show orderOf 5 = p−1 via the two prime factors 2 and 3 of p−1 = 3·2^30,
  -- then conclude (p−1) ∣ l from orderOf_dvd_of_pow_eq_one.
  have h_pm1 : mod64.toNat - 1 = 3 * 2 ^ 30 := by decide
  have horder : orderOf (primRoot.toNat : ZMod mod64.toNat) = mod64.toNat - 1 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by decide) PRIM_ROOT_pow_ZMod
    intro p hp hdvd
    rw [h_pm1] at hdvd
    rcases hp.dvd_mul.mp hdvd with h3 | h2pow
    · -- p ∣ 3, so p = 3; verify 5^((p−1)/3) ≠ 1
      have hp3 : p = 3 := by
        have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
        have hge : 2 ≤ p := hp.two_le
        interval_cases p
        · norm_num at h3
        · rfl
      subst hp3; exact prim_root_pow_div3_ne_one
    · -- p ∣ 2^30, so p = 2; verify 5^((p−1)/2) ≠ 1
      have hp2 : p = 2 := by
        have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h2pow
        have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
        have hge : 2 ≤ p := hp.two_le
        omega
      subst hp2; exact prim_root_pow_div2_ne_one
  exact horder ▸ orderOf_dvd_of_pow_eq_one hl

instance : Fact (Nat.Prime mod32.toNat) := ⟨prime_3221225473⟩
instance : Fact (Nat.Prime mod64.toNat) := ⟨mod32_eq_mod.symm ▸ prime_3221225473⟩

end NTT_Constants

/-!
# Montgomery arithmetic (R = 2^32, modulus p = mod64)
-/

/-
1.1  addMod32 computes (a + b) mod p exactly.
-/
theorem addmod32_correct (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    (addMod32 a b).toNat = (a.toNat + b.toNat) % mod32.toNat := by
  unfold addMod32 at *; simp_all only [ge_iff_le]
  split_ifs at *
  · rw [show (a - (mod32 - b) |> UInt32.toNat) =
            a.toNat - (mod32.toNat - b.toNat) % 2 ^ 32 from ?_]
    · rename_i h
      contrapose! h
      rw [UInt32.le_iff_toNat_le_toNat]
      rw [UInt32.toNat_sub]
      rw [show mod32.toNat = 3221225473 by rfl] at * ; omega
    · rw [UInt32.toNat_sub]
      rw [Nat.mod_eq_sub_mod]
      · rw [UInt32.toNat_sub]
        rw [show mod32.toNat = 3221225473 by rfl] at * ; omega
      · rw [tsub_add_eq_add_tsub]
        · exact le_tsub_of_add_le_left
            (by linarith [show (mod32 - b).toNat ≤ a.toNat from by assumption])
        · exact Nat.le_of_lt (UInt32.toNat_lt _)
  · have h_add : (a.toNat + b.toNat) < mod32.toNat := by
      rename_i h
      contrapose! h; simp_all only [UInt32.le_iff_toNat_le]
      rw [UInt32.toNat_sub]
      rw [Nat.mod_eq_sub_mod] <;> (norm_num [mod32] at * ; omega)
    norm_num [Nat.mod_eq_of_lt h_add]
    exact h_add.trans_le (by decide)

/-
1.2  subMod32 computes (a - b) mod p exactly.
-/
theorem submod32_correct (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    (subMod32 a b).toNat = (a.toNat + mod32.toNat - b.toNat) % mod32.toNat := by
  unfold subMod32
  split_ifs with h
  · simp_all only [UInt32.toNat_sub, UInt32.le_iff_toNat_le, ge_iff_le]
    have ha32 := a.toNat_lt; have hb32 := b.toNat_lt
    have hmod : mod32.toNat = 3221225473 := rfl
    rw [(by omega : 2 ^ 32 - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ 32),
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
        (by omega : a.toNat + mod32.toNat - b.toNat = (a.toNat - b.toNat) + mod32.toNat),
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · simp_all only [UInt32.toNat_add, UInt32.toNat_sub, UInt32.le_iff_toNat_le,
        ge_iff_le, not_le, Nat.reducePow]
    have ha32 := a.toNat_lt; have hb32 := b.toNat_lt
    have hmod : mod32.toNat = 3221225473 := rfl
    have h_inner : (4294967296 - b.toNat + a.toNat) % 4294967296 =
        4294967296 - b.toNat + a.toNat := Nat.mod_eq_of_lt (by omega)
    rw [h_inner]
    have h_simp :
        (4294967296 - b.toNat + a.toNat + mod32.toNat) % 4294967296 =
        (a.toNat + mod32.toNat - b.toNat) % 4294967296 := by
      rw [show 4294967296 - b.toNat + a.toNat + mod32.toNat
        = (a.toNat + mod32.toNat - b.toNat) + 4294967296 by
            linarith [
              Nat.sub_add_cancel (by linarith [(by decide : mod32.toNat ≤ 4294967296)] :
                b.toNat ≤ 4294967296),
              Nat.sub_add_cancel (by linarith [(by decide : mod32.toNat ≤ 4294967296)] :
                b.toNat ≤ a.toNat + mod32.toNat)]]
      norm_num [Nat.add_mod, Nat.mod_eq_of_lt]
    rw [h_simp, Nat.mod_eq_of_lt]
    · rw [Nat.mod_eq_of_lt]
      rw [tsub_lt_iff_left] <;> linarith [(by assumption : a.toNat < b.toNat)]
    · rw [tsub_lt_iff_left]
      · linarith [(by assumption : a.toNat < b.toNat),
                   (rfl : mod32.toNat = 3221225473)]
      · omega

/-
Key divisibility: T + m*mod64 ≡ 0 (mod 2^32)
-/
theorem mont_mul_nat_div32 (a b : ℕ) :
    let T := a * b
    let m := (T % 2^32 * montPprime.toNat) % 2^32
    (T + m * mod64.toNat) % 2^32 = 0 := by
  norm_num [montPprime, mod64]
  norm_num [UInt32.toNat, UInt64.toNat]
  omega

/-
S / 2^32 < 2 * mod64 when inputs < mod64
-/
theorem mont_mul_nat_u_bound (a b : ℕ)
    (ha : a < mod32.toNat) (hb : b < mod32.toNat) :
    let T := a * b
    let m := (T % 2^32 * montPprime.toNat) % 2^32
    (T + m * mod64.toNat) / 2^32 < 2 * mod64.toNat := by
  rw [Nat.div_lt_iff_lt_mul <| by decide]
  have h_bound : a * b < mod64.toNat^2 := by
    exact lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) (by decide)
  have h_bound : a * b % 2^32 * montPprime.toNat % 2^32 < 2^32 := by
    exact Nat.mod_lt _ (by decide)
  nlinarith [show mod64.toNat = 3221225473 by rfl]

/-
Step 1: UInt64 product doesn't overflow
-/
theorem mont_T_toNat (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    (a.toUInt64 * b.toUInt64).toNat = a.toNat * b.toNat := by
  norm_num [UInt64.toNat_mul]
  exact lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) (by decide)

/-
Step 2: m computation
-/
theorem mont_m_toNat (a b : UInt32) :
    ((a.toUInt64 * b.toUInt64).toUInt32 * montPprime).toNat =
      (a.toNat * b.toNat % 2^32 * montPprime.toNat) % 2^32 := by
  norm_num [UInt32.toNat_mul]

/-
Step 3: mp = m * mod64 doesn't overflow UInt64
-/
theorem mont_mp_toNat (a b : UInt32) :
    let m := (a.toUInt64 * b.toUInt64).toUInt32 * montPprime
    (m.toUInt64 * mod64).toNat = m.toNat * mod64.toNat := by
  -- Since $a$ and $b$ are both less than $2^{32}$, their product $a * b$ is less than $2^{64}$.
  have h_prod_lt : (a.toNat * b.toNat) % 2^32 * montPprime.toNat % 2^32 * mod64.toNat < 2^64 := by
    refine lt_of_le_of_lt
        (Nat.mul_le_mul (Nat.mod_lt _ (by decide) |> Nat.le_of_lt) le_rfl) ?_
    decide
  norm_num [UInt64.toNat_mul] at *
  simp [h_prod_lt]

/-
Step 4: u computation equals (T + mp) / 2^32
-/
theorem mont_u_toNat (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    let T := a.toUInt64 * b.toUInt64
    let m := T.toUInt32 * montPprime
    let mp := m.toUInt64 * mod64
    let lo := T.toUInt32.toUInt64 + mp.toUInt32.toUInt64
    let u := (T >>> 32) + (mp >>> 32) + (lo >>> 32)
    u.toNat = (a.toNat * b.toNat + m.toNat * mod64.toNat) / 2^32 := by
  have h_div_add_carry : ∀ (T_nat mp_nat : ℕ),
      T_nat < 2^64 → mp_nat < 2^64 →
      T_nat / 2^32 + mp_nat / 2^32 + (T_nat % 2^32 + mp_nat % 2^32) / 2^32 =
      (T_nat + mp_nat) / 2^32 := by
    omega
  convert h_div_add_carry _ _ _ _ using 1
  · simp +zetaDelta only [UInt64.toUInt32_mul, UInt32.toUInt32_toUInt64, UInt32.toUInt64_mul,
        UInt64.toUInt64_toUInt32, UInt64.toNat_add, UInt64.toNat_shiftRight, UInt64.toNat_mul,
        UInt32.toNat_toUInt64, Nat.reducePow, UInt64.reduceToNat, Nat.reduceMod, UInt64.toNat_mod,
        Nat.reduceDvd, Nat.mod_mod_of_dvd, Nat.mod_mul_mod, dvd_refl, Nat.mul_mod_mod,
        Nat.mod_add_mod, UInt32.toNat_mul] at *
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    · omega
    · exact lt_of_le_of_lt
          (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))))
          (by decide)
    · exact lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) (by decide)
    · omega
  · exact lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) (by decide)
  · have h_mul_lt : ∀ (x y : ℕ), x < 2^32 → y < 2^32 → x * y < 2^64 := by
      exact fun x y hx hy => by nlinarith
    apply h_mul_lt
    · exact UInt32.toNat_lt ((a.toUInt64 * b.toUInt64).toUInt32 * montPprime)
    · decide


-- Helper: define the pure-Nat Montgomery reduction
def montMulNat (a b : ℕ) : ℕ :=
  let T := a * b
  let m := (T % 2^32 * montPprime.toNat) % 2^32
  let S := T + m * mod64.toNat
  let u := S / 2^32
  u % mod64.toNat

lemma mont_cond_sub_mod (x : UInt64) (hx : x.toNat < 2 * mod64.toNat) :
    (if x ≥ mod64 then (x - mod64).toUInt32 else x.toUInt32).toNat = x.toNat % mod64.toNat := by
  by_cases h : x ≥ mod64
  · simp only [ge_iff_le, h, ite_true]
    have hmod : mod64.toNat = 3221225473 := rfl
    have hh : mod64.toNat ≤ x.toNat := UInt64.le_iff_toNat_le.mp h
    have hx64 := x.toNat_lt
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_sub]
    rw [(by omega : 2 ^ 64 - mod64.toNat + x.toNat = x.toNat - mod64.toNat + 2 ^ 64),
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_sub_mod hh]
    rw [Nat.mod_eq_of_lt (by omega : x.toNat - mod64.toNat < mod64.toNat)]
    rw [Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h, Nat.mod_eq_of_lt]
    · exact Nat.mod_eq_of_lt (show x.toNat < 2 ^ 32 from
          lt_of_lt_of_le (show x.toNat < mod64.toNat from lt_of_not_ge h) (by decide))
    · exact lt_of_not_ge h

/-
The UInt32 montMul equals montMulNat on toNat
-/
theorem mont_mul_eq_nat (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    (montMul a b).toNat = montMulNat a.toNat b.toNat := by
  unfold montMulNat
  field_simp
  rw [← mont_m_toNat a b]
  unfold montMul
  have h_u : (let T := a.toUInt64 * b.toUInt64
    let m := T.toUInt32 * montPprime
    let mp := m.toUInt64 * mod64
    let lo := T.toUInt32.toUInt64 + mp.toUInt32.toUInt64
    let u := T >>> 32 + mp >>> 32 + lo >>> 32
    u).toNat =
      (a.toNat * b.toNat +
        ((a.toUInt64 * b.toUInt64).toUInt32 * montPprime).toNat * mod64.toNat) / 2^32 := by
      apply mont_u_toNat a b ha hb
  have h_bound : (let T := a.toUInt64 * b.toUInt64
    let m := T.toUInt32 * montPprime
    let mp := m.toUInt64 * mod64
    let lo := T.toUInt32.toUInt64 + mp.toUInt32.toUInt64
    let u := T >>> 32 + mp >>> 32 + lo >>> 32
    u).toNat < 2 * mod64.toNat := by
      rw [h_u]
      rw [mont_m_toNat a b]
      exact mont_mul_nat_u_bound _ _ ha hb
  rw [mont_cond_sub_mod _ h_bound, h_u]

/-
montMulNat result is < mod64
-/
theorem mont_mul_nat_bound (a b : ℕ) : montMulNat a b < mod32.toNat :=
  Nat.mod_lt _ (by decide)

/-
montMulNat congruence: result * 2^32 ≡ a * b (mod mod64)
-/
theorem mont_mul_nat_congr (a b : ℕ) :
    montMulNat a b * 2^32 % mod32.toNat = a * b % mod32.toNat := by
  rw [montMulNat]
  rw [mod32_eq_mod] ; norm_num [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  norm_num [montPprime, mod32]
  norm_num [UInt32.toNat] ; omega

theorem mont_mul_correct (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    (montMul a b).toNat < mod32.toNat ∧
    (montMul a b).toNat * 2 ^ 32 % mod32.toNat = a.toNat * b.toNat % mod32.toNat := by
  rw [mont_mul_eq_nat a b ha hb]
  exact ⟨mont_mul_nat_bound a.toNat b.toNat,
         mont_mul_nat_congr a.toNat b.toNat⟩

/-
1.4  toMont enters the Montgomery domain: MontVal (toMont a) = a.toNat mod p.
Equivalently: (toMont a).toNat · R ≡ a · R² (mod p), and R² mod p = montR2.
-/
theorem to_mont_correct (a : UInt32) (ha : a.toNat < mod32.toNat) :
    (toMont a).toNat < mod32.toNat ∧
    (toMont a).toNat * 2 ^ 32 % mod32.toNat =
      a.toNat * (2 ^ 64 % mod32.toNat) % mod32.toNat := by
  convert mont_mul_correct a montR2 _ _ using 1
  · assumption
  · decide


