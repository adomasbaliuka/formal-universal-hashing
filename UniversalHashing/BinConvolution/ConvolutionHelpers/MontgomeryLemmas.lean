/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import Batteries.Data.BitVec.Lemmas
public import Batteries.Data.UInt
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic.NormNum.Prime
public import UniversalHashing.BinConvolution.ConvolutionDefs


/-!
# Constants
-/

@[expose] public section
section NTT_Constants


theorem prime_3221225473 : Nat.Prime 3221225473 := by norm_num

theorem mod32_eq_mod : mod64.toNat = mod32.toNat := by decide

theorem prime_mod : mod64.toNat.Prime := prime_3221225473

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

/-
`powModAuxU64` correctly computes `r * b^e % mod_` when `b < mod_` and `r < mod_`
    and `mod_` is small enough to avoid UInt64 overflow (mod_ ≤ 2^32).
-/
lemma powmodAux_correct (mod_ : UInt64) (f : ℕ) (b e r : UInt64)
    (hmod : 1 < mod_.toNat) (hmod_small : mod_.toNat ≤ 2 ^ 32)
    (hb : b.toNat < mod_.toNat) (hr : r.toNat < mod_.toNat)
    (hf : e.toNat < 2 ^ f) :
    (powModAuxU64 mod_ f b e r).toNat = (r.toNat * b.toNat ^ e.toNat) % mod_.toNat := by
  induction f generalizing b e r with
  | zero =>
    simp_all only [powModAuxU64, Nat.lt_one_iff, pow_zero, mul_one]
    rw [Nat.mod_eq_of_lt hr]
  | succ f ih =>
    unfold powModAuxU64
    norm_num at hmod_small
    simp only [beq_iff_eq, bne_iff_ne, pow_succ'] at *
    split_ifs
    · simp_all only [pow_zero, mul_one, Nat.mod_eq_of_lt hr, UInt64.toNat_zero]
    · rw [ih]
      · rw [show e.toNat = 2 * (e >>> 1 |> UInt64.toNat) + 1 from ?_]
        · norm_num [
              ← ZMod.natCast_eq_natCast_iff',
              Nat.mod_eq_of_lt (by linarith : b.toNat < 18446744073709551616),
              Nat.mod_eq_of_lt (by linarith : r.toNat < 18446744073709551616)]
          ring_nf
          norm_num [pow_mul', ← ZMod.natCast_eq_natCast_iff']
          norm_num [
            Nat.mod_eq_of_lt ((by nlinarith : r.toNat * b.toNat < 18446744073709551616)),
            Nat.mod_eq_of_lt ((by nlinarith : b.toNat ^ 2 < 18446744073709551616))]
        · cases Nat.mod_two_eq_zero_or_one e.toNat <;>
              simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
                         (by decide : (1 : UInt64).toNat % 64 = 1)] at *
          · cases e ; simp_all only [UInt64.toNat_ofBitVec]
            rename_i k hk₁ hk₂ hk₃
            contrapose! hk₂
            ext
            simp [hk₃]
          · omega
      · -- By definition of modulo, the result of any number modulo mod_ is always less than mod_.
        have h_mod : ∀ (n : UInt64), (n % mod_).toNat < mod_.toNat := by
          intro n
          rw [UInt64.toNat_mod]
          exact Nat.mod_lt _ (pos_of_gt hmod)
        exact h_mod _
      · simp only [UInt64.toNat_mod, UInt64.toNat_mul, Nat.reducePow]
        exact Nat.mod_lt _ (by linarith)
      · simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
                   (by decide : (1 : UInt64).toNat % 64 = 1), pow_one]
        omega
    · simp only [not_ne_iff] at *
      convert ih (b * b % mod_) (e >>> 1) r _ _ _ using 1
      · rw [show e.toNat = 2 * (e.toNat / 2) by
              rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero _)]
              rw [← Nat.even_iff]
              rw [Nat.even_iff]
              replace := congr_arg (fun x : UInt64 => x.toNat) ‹e &&& 1 = 0›
              norm_num [Nat.and_comm] at this ⊢ ; aesop;] ;
            norm_num [pow_mul, Nat.mul_mod, Nat.pow_mod]
        norm_num [← Nat.mul_mod, ← Nat.pow_mod]
        rw [← sq]
        rw [Nat.mod_eq_of_lt ((by nlinarith : b.toNat ^ 2 < 18446744073709551616))] ; rfl
      · exact Nat.mod_lt _ (by positivity)
      · assumption
      · convert Nat.div_lt_of_lt_mul <| show e.toNat < 2 * 2 ^ f from hf using 1
        simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

/-
`powModU64 base exp mod_` correctly computes `base^exp % mod_` when mod_ ≤ 2^32.
-/
lemma powmod_correct (base exp mod_ : UInt64)
    (hmod : 1 < mod_.toNat) (hmod_small : mod_.toNat ≤ 2 ^ 32) :
    (powModU64 base exp mod_).toNat = base.toNat ^ exp.toNat % mod_.toNat := by
  unfold powModU64
  rw [powmodAux_correct]
  any_goals assumption
  · simp [← ZMod.natCast_eq_natCast_iff', Nat.cast_pow]
  · exact Nat.mod_lt _ (pos_of_gt hmod)
  · exact exp.toNat_lt

private lemma zmod_cast_pow_eq_powModU64_cast (a e p : UInt64) (a' e' n : ℕ)
    (ha : a' = a.toNat) (he : e' = e.toNat) (hn : n = p.toNat)
    (hmod : 1 < p.toNat) (hp : p.toNat ≤ 2 ^ 32) :
    ((a' : ZMod n)) ^ e' = ((powModU64 a e p).toNat : ZMod n) := by
  subst ha he hn
  rw [powmod_correct a e p hmod hp, ZMod.natCast_mod, Nat.cast_pow]

private lemma prim_root_pow_div3_ne_one :
    (primRoot.toNat : ZMod mod64.toNat) ^ ((mod64.toNat - 1) / 3) ≠ 1 := by
  rw [(by decide : primRoot.toNat = 5),
      (by decide : mod64.toNat = 3221225473),
      (by decide : (3221225473 - 1) / 3 = 1073741824)]
  rw [zmod_cast_pow_eq_powModU64_cast 5 1073741824 3221225473 5 1073741824 3221225473
        (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [(by decide : (powModU64 5 1073741824 3221225473).toNat = 1610563584)]
  decide

/-- `primRoot^{(mod64-1)/2} = -1` in `ZMod mod32.toNat`. -/
lemma prim_root_half_eq_neg_one :
    (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2) = -1 := by
  rw [(by decide : primRoot.toNat = 5),
      (by decide : mod32.toNat = 3221225473),
      (by decide : mod64.toNat = 3221225473),
      (by decide : (3221225473 - 1) / 2 = 1610612736)]
  rw [zmod_cast_pow_eq_powModU64_cast 5 1610612736 3221225473 5 1610612736 3221225473
        (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [(by decide : (powModU64 5 1610612736 3221225473).toNat = 3221225472)]
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
Step 2: m computation
-/
theorem mont_m_toNat (a b : UInt32) :
    ((a.toUInt64 * b.toUInt64).toUInt32 * montPprime).toNat =
      (a.toNat * b.toNat % 2^32 * montPprime.toNat) % 2^32 := by
  norm_num [UInt32.toNat_mul]

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
  · rfl
  · rw [show montR2.toNat = 2 ^ 64 % mod32.toNat from by decide]
    rfl
  · assumption
  · decide

end
