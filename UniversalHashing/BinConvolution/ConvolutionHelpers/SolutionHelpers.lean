/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib
import PrimeCert
import UniversalHashing.BinConvolution.ConvolutionHelpers.DFTLemmas
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
  rw [show primRoot.toNat = 5 from by decide,
      show mod64.toNat = 3221225473 from by decide,
      show (3221225473 - 1) / 3 = 1073741824 from by decide]
  rw [show powMod 5 1073741824 3221225473 = 1610563584 from by prove_pow_mod]
  decide

/-- `primRoot^{(mod64-1)/2} = -1` in `ZMod mod32.toNat`. -/
lemma prim_root_half_eq_neg_one :
    (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2) = -1 := by
  rw [zmod_cast_pow_eq_powMod_cast]
  rw [show primRoot.toNat = 5 from by decide,
      show mod32.toNat = 3221225473 from by decide,
      show mod64.toNat = 3221225473 from by decide,
      show (3221225473 - 1) / 2 = 1610612736 from by decide]
  rw [show powMod 5 1610612736 3221225473 = 3221225472 from by prove_pow_mod]
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
  · rw [ show ( a - ( mod32 - b ) |> UInt32.toNat ) =
            a.toNat - ( mod32.toNat - b.toNat ) % 2 ^ 32 from ?_ ]
    · rename_i h
      contrapose! h
      rw [ UInt32.le_iff_toNat_le_toNat ]
      rw [ UInt32.toNat_sub ]
      rw [ show mod32.toNat = 3221225473 by rfl ] at * ; omega
    · rw [ UInt32.toNat_sub ]
      rw [ Nat.mod_eq_sub_mod ]
      · rw [ UInt32.toNat_sub ]
        rw [ show mod32.toNat = 3221225473 by rfl ] at * ; omega
      · rw [ tsub_add_eq_add_tsub ]
        · exact le_tsub_of_add_le_left
            ( by linarith [ show ( mod32 - b ).toNat ≤ a.toNat from by assumption ] )
        · exact Nat.le_of_lt ( UInt32.toNat_lt _ )
  · have h_add : (a.toNat + b.toNat) < mod32.toNat := by
      rename_i h
      contrapose! h; simp_all only [UInt32.le_iff_toNat_le]
      rw [ UInt32.toNat_sub ]
      rw [ Nat.mod_eq_sub_mod ] <;> (norm_num [ mod32 ] at * ; omega)
    norm_num [ Nat.mod_eq_of_lt h_add ]
    exact h_add.trans_le ( by decide )

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
    rw [show 2 ^ 32 - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ 32 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
        show a.toNat + mod32.toNat - b.toNat = (a.toNat - b.toNat) + mod32.toNat from by omega,
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
      rw [ show 4294967296 - b.toNat + a.toNat + mod32.toNat
        = ( a.toNat + mod32.toNat - b.toNat ) + 4294967296 by
            linarith [
              Nat.sub_add_cancel ( show b.toNat ≤ 4294967296 from by
                linarith [ show mod32.toNat ≤ 4294967296 from by decide ] ),
              Nat.sub_add_cancel ( show b.toNat ≤ a.toNat + mod32.toNat from by
                linarith [ show mod32.toNat ≤ 4294967296 from by decide ] ) ] ]
      norm_num [ Nat.add_mod, Nat.mod_eq_of_lt ]
    rw [ h_simp, Nat.mod_eq_of_lt ]
    · rw [ Nat.mod_eq_of_lt ]
      rw [ tsub_lt_iff_left ] <;> linarith [ show a.toNat < b.toNat from by assumption ]
    · rw [ tsub_lt_iff_left ]
      · linarith [ show a.toNat < b.toNat from by assumption,
                   show mod32.toNat = 3221225473 from by rfl ]
      · grind +splitIndPred

/-
Key divisibility: T + m*mod64 ≡ 0 (mod 2^32)
-/
theorem mont_mul_nat_div32 (a b : ℕ) :
    let T := a * b
    let m := (T % 2^32 * montPprime.toNat) % 2^32
    (T + m * mod64.toNat) % 2^32 = 0 := by
  norm_num [ montPprime, mod64 ]
  norm_num [ UInt32.toNat, UInt64.toNat ]
  grind

/-
S / 2^32 < 2 * mod64 when inputs < mod64
-/
theorem mont_mul_nat_u_bound (a b : ℕ)
    (ha : a < mod32.toNat) (hb : b < mod32.toNat) :
    let T := a * b
    let m := (T % 2^32 * montPprime.toNat) % 2^32
    (T + m * mod64.toNat) / 2^32 < 2 * mod64.toNat := by
  rw [ Nat.div_lt_iff_lt_mul <| by decide ]
  have h_bound : a * b < mod64.toNat^2 := by
    exact lt_of_lt_of_le ( Nat.mul_lt_mul'' ha hb ) ( by decide )
  have h_bound : a * b % 2^32 * montPprime.toNat % 2^32 < 2^32 := by
    exact Nat.mod_lt _ ( by decide )
  nlinarith [ show mod64.toNat = 3221225473 by rfl ]

/-
Step 1: UInt64 product doesn't overflow
-/
theorem mont_T_toNat (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    (a.toUInt64 * b.toUInt64).toNat = a.toNat * b.toNat := by
  norm_num [ UInt64.toNat_mul ]
  exact lt_of_lt_of_le ( Nat.mul_lt_mul'' ha hb ) ( by decide )

/-
Step 2: m computation
-/
theorem mont_m_toNat (a b : UInt32) :
    ((a.toUInt64 * b.toUInt64).toUInt32 * montPprime).toNat =
      (a.toNat * b.toNat % 2^32 * montPprime.toNat) % 2^32 := by
  norm_num [ UInt32.toNat_mul ]

/-
Step 3: mp = m * mod64 doesn't overflow UInt64
-/
theorem mont_mp_toNat (a b : UInt32) :
    let m := (a.toUInt64 * b.toUInt64).toUInt32 * montPprime
    (m.toUInt64 * mod64).toNat = m.toNat * mod64.toNat := by
  -- Since $a$ and $b$ are both less than $2^{32}$, their product $a * b$ is less than $2^{64}$.
  have h_prod_lt : (a.toNat * b.toNat) % 2^32 * montPprime.toNat % 2^32 * mod64.toNat < 2^64 := by
    refine lt_of_le_of_lt
        ( Nat.mul_le_mul ( Nat.mod_lt _ ( by decide ) |> Nat.le_of_lt ) le_rfl ) ?_
    decide
  norm_num [ UInt64.toNat_mul ] at *
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
    rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ]
    · omega
    · exact lt_of_le_of_lt
          ( Nat.mul_le_mul_right _ ( Nat.le_of_lt_succ ( Nat.mod_lt _ ( by decide ) ) ) )
          ( by decide )
    · exact lt_of_lt_of_le ( Nat.mul_lt_mul'' ha hb ) ( by decide )
    · omega
  · exact lt_of_lt_of_le ( Nat.mul_lt_mul'' ha hb ) ( by decide )
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

/-
The UInt32 montMul equals montMulNat on toNat
-/
theorem mont_mul_eq_nat (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    (montMul a b).toNat = montMulNat a.toNat b.toNat := by
  unfold montMulNat
  field_simp
  rw [ ← mont_m_toNat a b ]
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
      rw [ mont_m_toNat a b ]
      exact mont_mul_nat_u_bound _ _ ha hb
  have h_mod : ∀ (x : UInt64), x.toNat < 2 * mod64.toNat →
      (if x ≥ mod64 then (x - mod64).toUInt32 else x.toUInt32).toNat = x.toNat % mod64.toNat := by
    intros x hx
    by_cases h : x ≥ mod64
    · simp only [ge_iff_le, h, ite_true]
      have hmod : mod64.toNat = 3221225473 := rfl
      have hh : mod64.toNat ≤ x.toNat := UInt64.le_iff_toNat_le.mp h
      have hx64 := x.toNat_lt
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_sub]
      rw [show 2 ^ 64 - mod64.toNat + x.toNat = x.toNat - mod64.toNat + 2 ^ 64 from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_sub_mod hh]
      rw [Nat.mod_eq_of_lt (by omega : x.toNat - mod64.toNat < mod64.toNat)]
      rw [Nat.mod_eq_of_lt (by omega)]
    · rw [ if_neg h, Nat.mod_eq_of_lt ]
      · exact Nat.mod_eq_of_lt ( show x.toNat < 2 ^ 32 from
            lt_of_lt_of_le ( show x.toNat < mod64.toNat from lt_of_not_ge h )
            ( by decide ) )
      · exact lt_of_not_ge h
  rw [ h_mod _ h_bound, h_u ]

/-
montMulNat result is < mod64
-/
theorem mont_mul_nat_bound (a b : ℕ) : montMulNat a b < mod32.toNat :=
  Nat.mod_lt _ ( by decide )

/-
montMulNat congruence: result * 2^32 ≡ a * b (mod mod64)
-/
theorem mont_mul_nat_congr (a b : ℕ) :
    montMulNat a b * 2^32 % mod32.toNat = a * b % mod32.toNat := by
  rw [ montMulNat ]
  rw [ mod32_eq_mod ] ; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_mod ]
  norm_num [ montPprime, mod32 ]
  norm_num [ UInt32.toNat ] ; omega

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


/-!
#  ── Root table
-/

/-
`rootsInner wm halfLen k 0 v` sets position `halfLen + j` to `montPow v[halfLen] wm j`
for every `j ≤ k` (provided indices are in bounds).
-/
lemma rootsInner_montPow (wm : UInt32) (halfLen : ℕ) {n : ℕ}
    (k j : ℕ) (v : Vector UInt32 n) (hj : j ≤ k) (hn : halfLen + k < n) :
    (rootsInner wm halfLen k 0 v)[halfLen + j]'(by omega) =
      montPow (v[halfLen]'(by omega)) wm j := by
  revert v j;
  induction k generalizing halfLen with
  | zero =>
    -- In the base case where `k = 0`, `rootsInner` returns `v` unchanged.
    intros j v hj
    simp only [rootsInner];
    interval_cases j ; aesop -- grind +locals -- used to work before splitting file into multiple...
  | succ k ih =>
    intro j v hj
    by_cases hj0 : j = 0;
    · rw [ rootsInner ];
      split_ifs <;> simp_all only [zero_add, add_zero];
      · have h_preserve : ∀ (k : ℕ) (i : ℕ) (v : Vector UInt32 n),
              (rootsInner wm halfLen k i v)[halfLen]'(by linarith) =
              v[halfLen]'(by linarith) := by
          intros k i v; exact (by
          induction k generalizing i v with
          | zero => simp_all only [rootsInner]
          | succ k ih => simp_all only [rootsInner]; grind);
        rw [ h_preserve ];
        rw [ Vector.getElem_set ] ; aesop;
      · linarith;
      · linarith;
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := Nat.exists_eq_succ_of_ne_zero hj0;
      convert ih ( halfLen + 1 ) ( by linarith ) j'
          ( rootsInner wm halfLen 1 0 v ) ( by linarith ) using 1;
      · rw [ show rootsInner wm halfLen ( k + 1 ) 0 v =
                  rootsInner wm ( halfLen + 1 ) k 0 ( rootsInner wm halfLen 1 0 v ) from ?_ ];
        · ac_rfl;
        · -- By definition of `rootsInner`, we can split the application into two parts.
          have h_split : ∀ (k : ℕ) (i : ℕ) (v : Vector UInt32 n),
              rootsInner wm halfLen (k + 1) i v =
              rootsInner wm (halfLen + 1) k i (rootsInner wm halfLen 1 i v) := by
            intros k i v;
            induction k generalizing i v with
            | zero => simp_all only [rootsInner]
            | succ k ih => simp_all only [rootsInner]; grind +qlia;
          exact h_split k 0 v;
      · rw [ show rootsInner wm halfLen 1 0 v =
                  v.set ( halfLen + 1 ) ( montMul ( v[halfLen] ) wm )
                    ( by linarith ) from ?_ ];
        · all_goals generalize_proofs at *;
          simp only [Vector.getElem_set_self, montPow];
          exact Nat.recOn j' rfl fun n ihn => by
            rw [ show montPow ( montMul v[halfLen] wm ) wm ( n + 1 ) =
                    montMul ( montPow ( montMul v[halfLen] wm ) wm n ) wm from rfl,
                 show montPow v[halfLen] wm ( n + 1 ) =
                    montMul ( montPow v[halfLen] wm n ) wm from rfl, ihn ] ;
        · all_goals generalize_proofs at *;
          simp [ rootsInner ];
          aesop

/-
`rootsInner` does not modify positions at index ≤ `halfLen + i`.
-/
lemma rootsInner_preserves_below (wm : UInt32) (halfLen : ℕ) {n : ℕ}
    (k i pos : ℕ) (v : Vector UInt32 n) (hpos : pos < n) (h : pos ≤ halfLen + i) :
    (rootsInner wm halfLen k i v)[pos]'hpos = v[pos]'hpos := by
  induction k generalizing i v with
  | zero => rfl
  | succ k ih => unfold rootsInner; grind

/-
`rootsInner` does not modify positions strictly above `halfLen + i + k`.
-/
lemma rootsInner_preserves_above (wm : UInt32) (halfLen : ℕ) {n : ℕ}
    (k i pos : ℕ) (v : Vector UInt32 n) (hpos : pos < n) (h : pos > halfLen + i + k) :
    (rootsInner wm halfLen k i v)[pos]'hpos = v[pos]'hpos := by
  induction k generalizing i v with
  | zero => rfl
  | succ k ih => rw [ rootsInner ]; grind

/-
When `wm.toNat = (w * montR1.toNat) % mod64`, the iterated product satisfies
`(montPow montR1 wm j).toNat = (w ^ j * montR1.toNat) % mod64`.
This is the Montgomery-domain geometric series: montR1 = R, and multiplying by
`wm = w·R` (in Montgomery domain) advances the power of `w` by one each step.
-/
lemma montPow_spec (wm : UInt32) (w j : ℕ)
    (hwm : wm.toNat = (w * montR1.toNat) % mod32.toNat) :
    (montPow montR1 wm j).toNat = (w ^ j * montR1.toNat) % mod32.toNat := by
  have h_ind :
      ∀ (j : ℕ), (montPow montR1 wm j).toNat ≡ w ^ j * montR1.toNat [MOD mod32.toNat] := by
    intro j
    have h_ind_step :
        ∀ (j : ℕ), (montPow montR1 wm (j + 1)).toNat =
          montMulNat (montPow montR1 wm j).toNat wm.toNat := by
      intro j
      rw [montPow];
      apply mont_mul_eq_nat;
      · induction j with
        | zero => exact show montR1.toNat < mod32.toNat from by decide
        | succ j ih =>
          exact mont_mul_correct _ _ ih
              ( show wm.toNat < mod32.toNat from hwm.symm ▸ Nat.mod_lt _ ( by decide ) )
              |>.1 |> fun h => by simpa [ montPow ] using h;
      · exact hwm.symm ▸ Nat.mod_lt _ ( by decide );
    induction j with
    | zero => simp +decide [ montPow ]
    | succ j ih =>
      have h_ind_step :
          montMulNat (montPow montR1 wm j).toNat wm.toNat * 2 ^ 32 ≡
          (montPow montR1 wm j).toNat * wm.toNat [MOD mod32.toNat] := by
        apply mont_mul_nat_congr;
      have h_ind_step :
          montMulNat (montPow montR1 wm j).toNat wm.toNat * 2 ^ 32 ≡
          w ^ (j + 1) * montR1.toNat * 2 ^ 32 [MOD mod32.toNat] := by
        simp_all +decide only [← ZMod.natCast_eq_natCast_iff, mul_assoc, Nat.cast_mul,
                               Nat.cast_pow, Nat.reducePow, ZMod.natCast_mod]
        rw [ MONT_R1_ZMod ] ; ring;
      simp_all only [Nat.modEq_iff_dvd, Nat.cast_mul, Nat.cast_pow, Nat.reducePow]
      have h_ind_step : (mod32.toNat : ℤ) ∣
          (w ^ (j + 1) * montR1.toNat -
            montMulNat (montPow montR1 wm j).toNat (w * montR1.toNat % mod32.toNat)) *
          4294967296 := by
        convert h_ind_step using 1 ; ring;
      exact ( Int.dvd_of_dvd_mul_left_of_gcd_one h_ind_step <| by decide );
  rw [ ← h_ind j, Nat.mod_eq_of_lt ];
  induction j with
  | zero => exact show montR1.toNat < mod32.toNat from by decide
  | succ j ih =>
    have := mont_mul_correct (montPow montR1 wm j) wm ih (by
      exact hwm.symm ▸ Nat.mod_lt _ ( by decide ));
    exact this.1

lemma nat_toUInt64_faithful (m : ℕ) (hm : m < 2 ^ 64) : m.toUInt64.toNat = m := by
  simp only [Nat.toUInt64, UInt64.toNat, UInt64.ofNat, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hm

lemma pow2_toUInt64_le (s : ℕ) (n : UInt64) (hs : s < 64)
    (h : 2 ^ (s + 1) ≤ n.toNat) : ¬((2 ^ (s + 1) : ℕ).toUInt64 > n) := by
  interval_cases s <;> aesop

/-- ℕ-variant: `(2^(s+1)).toUInt64.toNat = 2^(s+1)` when `s < 63`, so `≤ n` in ℕ. -/
lemma pow2_toUInt64_le_nat (s n : ℕ) (hs : s < 63) (h : 2 ^ (s + 1) ≤ n) :
    ¬(((2 ^ (s + 1) : ℕ).toUInt64).toNat > n) := by
  have key : ((2 ^ (s + 1) : ℕ).toUInt64).toNat = 2 ^ (s + 1) := by
    interval_cases s <;> decide
  omega

lemma pow2_toUInt64_halfLen (s : ℕ) (hs : s < 63) :
    ((2 ^ (s + 1) : ℕ).toUInt64 / 2).toNat = 2 ^ s := by
  interval_cases s <;> decide

lemma pow2_toUInt64_shift (s : ℕ) (hs : s < 63) :
    ((2 ^ (s + 1) : ℕ).toUInt64 <<< 1) = (2 ^ (s + 2) : ℕ).toUInt64 := by
  interval_cases s <;> trivial

/-
When `len = 0`, the outer loop only modifies position 0.
Any position `pos ≥ 1` is preserved.
-/
lemma outer_zero_preserves (n : ℕ) (v : Vector UInt32 n) (hn : 0 < n)
    (f : ℕ) (pos : ℕ) (hpos : pos < n) (hge1 : 1 ≤ pos) :
    (ensureRoots.outer n v 0 hn f)[pos]'hpos = v[pos]'hpos := by
  induction f generalizing v with
  | zero => rfl
  | succ f ih =>
    unfold ensureRoots.outer;
    rcases pos with ( _ | pos ) <;> simp_all [ rootsInner ]


/-
After the target iteration, subsequent iterations of the outer loop
preserve position `2^K + j` because all subsequent halfLens are > 2^K + j.
-/
lemma outer_preserves_target (n : ℕ) (hN : 0 < n)
    (v : Vector UInt32 n) (s f K j : ℕ)
    (hs_gt_K : s > K) (hj : j < 2 ^ K)
    (hKn : 2 ^ K + j < n)
    (hs_lt : s < 64) :
    (ensureRoots.outer n v ((2 ^ (s + 1) : ℕ).toUInt64) hN f)[2 ^ K + j]'hKn =
      v[2 ^ K + j]'hKn := by
  induction f generalizing v s with
  | zero => simp [ensureRoots.outer]
  | succ f ih =>
    have hpos_ge_one : 1 ≤ 2 ^ K + j := by
      rcases Nat.eq_zero_or_pos K with hK0 | hK1
      · subst hK0; simp at hj; omega
      · have h2K : 2 ≤ 2 ^ K := calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK1
        omega
    by_cases hs63 : s < 63
    · have h_halfLen : ((2 ^ (s + 1) : ℕ).toUInt64 / 2).toNat = 2 ^ s :=
        pow2_toUInt64_halfLen s hs63
      have h_K_lt_s : 2 ^ K + j < 2 ^ s := by
        have h1 : 2 ^ K + j < 2 ^ (K + 1) := by
          have hpow : 2 ^ (K + 1) = 2 ^ K + 2 ^ K := by rw [pow_succ]; ring
          omega
        exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hs_gt_K)
      have h_neq : 2 ^ K + j ≠ ((2 ^ (s + 1) : ℕ).toUInt64 / 2).toNat := by
        rw [h_halfLen]; omega
      have h_le : 2 ^ K + j ≤ ((2 ^ (s + 1) : ℕ).toUInt64 / 2).toNat + 0 := by
        rw [h_halfLen]; omega
      have h_shift : ((2 ^ (s + 1) : ℕ).toUInt64 <<< 1) = (2 ^ (s + 2) : ℕ).toUInt64 :=
        pow2_toUInt64_shift s hs63
      unfold ensureRoots.outer
      split_ifs with h_gt
      · rfl
      · simp only [h_shift, ih _ (s + 1) (by omega) (by omega),
          rootsInner_preserves_below _ _ _ _ _ _ hKn h_le,
          Vector.getElem_set, Ne.symm h_neq, if_false]
    · have hs_eq : s = 63 := by omega
      subst hs_eq
      have h_half_eq : ((2 ^ (63 + 1) : ℕ).toUInt64 / 2).toNat = 0 := by decide
      have h_shift_eq : ((2 ^ (63 + 1) : ℕ).toUInt64 <<< 1) = (2 ^ (63 + 1) : ℕ).toUInt64 := by
        decide
      have h_inner_id : ∀ (wm : UInt32) {N : ℕ} (i : ℕ) (v0 : Vector UInt32 N),
          rootsInner wm 0 0 i v0 = v0 := fun wm _ i v0 => by unfold rootsInner; rfl
      unfold ensureRoots.outer
      split_ifs with h_gt
      · rfl
      · simp only [h_half_eq, h_inner_id, h_shift_eq,
          ih _ 63 hs_gt_K (by omega),
          Vector.getElem_set,
          show (0 : ℕ) ≠ 2 ^ K + j from by omega, if_false]

/-
`powModU64 base exp mod_` computes `base.toNat ^ exp.toNat % mod_.toNat` (Nat values).
    Correctness of the binary-exponentiation loop in `powModAuxU64`.
    The condition `mod_.toNat ≤ 2^32` ensures no UInt64 overflow in intermediate
    multiplications (since all intermediate values are < mod_ ≤ 2^32).
-/
lemma powmod_spec (base exp mod_ : UInt64) (hmod : 1 < mod_.toNat)
    (hmod_small : mod_.toNat ≤ 2 ^ 32) :
    (powModU64 base exp mod_).toNat = base.toNat ^ exp.toNat % mod_.toNat := by
  -- The provided solution is incorrect. The correct solution is to use the provided solution.
  by_contra h_contra;
  have h_inv :
      ∀ (f : ℕ) (b e r : UInt64),
      1 < mod_.toNat → mod_.toNat ≤ 2^32 →
      b.toNat < mod_.toNat → e.toNat < 2^f → r.toNat < mod_.toNat →
      (powModAuxU64 mod_ f b e r).toNat = (r.toNat * b.toNat ^ e.toNat) % mod_.toNat := by
    intros f b e r hmod hmod_small hb he hr
    induction f generalizing b e r with
    | zero =>
      simp_all only [powModAuxU64, Nat.lt_one_iff, pow_zero, mul_one]
      rw [Nat.mod_eq_of_lt hr]
    | succ f ih =>
      unfold powModAuxU64
      norm_num at hmod_small
      simp only [beq_iff_eq, bne_iff_ne, ne_eq, ite_not] at *
      split_ifs <;>
        simp_all +decide only [pow_succ, pow_zero, mul_one, Nat.mod_eq_of_lt hr, UInt64.toNat_zero]
      · convert ih ( b * b % mod_ ) ( e >>> 1 ) r _ _ _ using 1;
        · rw [ show e.toNat = 2 * ( e.toNat / 2 ) by
                rw [ Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero _ ) ];
                rw [ ← UInt64.toNat_inj ] at * ; aesop ] ; ring_nf;
          norm_num [ pow_mul', Nat.mul_mod, Nat.pow_mod ];
          norm_num [ ← Nat.mul_mod, ← Nat.pow_mod ];
          rw [ ← sq ];
          rw [ Nat.mod_eq_of_lt
                 ( show b.toNat ^ 2 < 18446744073709551616 from by nlinarith ) ] ; rfl;
        · exact Nat.mod_lt _ hmod.le;
        · simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
                     show (1 : UInt64).toNat % 64 = 1 from by decide];
          exact Nat.div_lt_of_lt_mul <| by linarith;
        · assumption;
      · convert ih ( b * b % mod_ ) ( e >>> 1 ) ( r * b % mod_ ) _ _ _ using 1;
        · rw [ show e.toNat = 2 * ( e >>> 1 ).toNat + 1 from ?_ ];
          · simp +decide [ ← ZMod.natCast_eq_natCast_iff', pow_add, pow_mul ];
            ring_nf;
            norm_num [ pow_mul', ← ZMod.natCast_eq_natCast_iff' ];
            norm_num [
              Nat.mod_eq_of_lt ( show r.toNat * b.toNat < 18446744073709551616 from by nlinarith ),
              Nat.mod_eq_of_lt ( show b.toNat ^ 2 < 18446744073709551616 from by nlinarith ) ];
          · cases Nat.mod_two_eq_zero_or_one e.toNat <;>
              simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
                         show (1 : UInt64).toNat % 64 = 1 from by decide] at *;
            · cases e ; simp_all +decide only [UInt64.toNat_ofBitVec, pow_one] ;
              rename_i k hk₁ hk₂ hk₃;
              cases hk₂ (by rw [← UInt64.toNat_inj]; simp +decide [hk₃]);
            · omega;
        · exact Nat.mod_lt _ hmod.le;
        · simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
                     show (1 : UInt64).toNat % 64 = 1 from by decide];
          exact Nat.div_lt_of_lt_mul <| by linarith;
        · exact Nat.mod_lt _ ( by positivity );
  apply h_contra;
  convert h_inv 64 ( base % mod_ ) exp 1 hmod hmod_small _ _ _ using 1;
  · simp +decide [ ← ZMod.natCast_eq_natCast_iff' ];
  · exact Nat.mod_lt _ ( by positivity );
  · exact exp.toNat_lt;
  · exact hmod

/-- `toMont a` computes `a.toNat * montR1.toNat % mod32.toNat` at the Nat level. -/
lemma to_mont_nat_helper (x a : ℕ) (hx_lt : x < mod32.toNat)
    (h_cong : x * 2 ^ 32 % mod32.toNat = a * (2 ^ 64 % mod32.toNat) % mod32.toNat) :
    x = a * montR1.toNat % mod32.toNat := by
  have hp : mod32.toNat = 3221225473 := rfl
  have hR1 : montR1.toNat = 1073741823 := rfl
  have hR2 : (2^64 % mod32.toNat) = 1789569709 := by decide
  rw [hR2] at h_cong
  rw [hp] at h_cong ⊢; rw [hR1]
  have h_rel : a * 1789569709 % 3221225473 = (a * 1073741823) * 2^32 % 3221225473 := by
    have : 1789569709 % 3221225473 = (1073741823 * 2^32) % 3221225473 := by decide
    rw [Nat.mul_mod, this, ← Nat.mul_mod, Nat.mul_assoc]
  have h1 : x * 2^32 ≡ (a * 1073741823) * 2^32 [MOD 3221225473] := by
    rw [Nat.ModEq]; rw [h_cong, h_rel]
  have h_coprime : Nat.gcd 3221225473 (2^32) = 1 := by decide
  exact (Nat.mod_eq_of_lt (hp ▸ hx_lt)).symm ▸ (Nat.ModEq.cancel_right_of_coprime h_coprime h1)

lemma to_mont_nat (a : UInt32) (ha : a.toNat < mod32.toNat) :
    (toMont a).toNat = a.toNat * montR1.toNat % mod32.toNat := by
  exact to_mont_nat_helper _ _ (to_mont_correct a ha).1 (to_mont_correct a ha).2

/-- Casting a UInt64 value below 2^32 to UInt32 and back preserves the Nat value. -/
lemma UInt64_toUInt32_toNat (x : UInt64) (hx : x.toNat < 2 ^ 32) :
    x.toUInt32.toNat = x.toNat := by
  simp_all only [Nat.reducePow, UInt64.toNat_toUInt32, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
    Nat.reduceAdd]

/--
The s = K base step of ensure_roots_outer_inv: after one outer-loop iteration at level K,
followed by any number of further iterations, position 2^K+j holds (w^j · montR1) % mod64.
-/
lemma ensure_roots_base_case (n : ℕ) (hN : 0 < n)
    (v : Vector UInt32 n) (K j f : ℕ)
    (hlen_K : 2 ^ (K + 1) ≤ n) (hj : j < 2 ^ K) (hK63 : K < 63)
    (h_half : ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat < n)
    (hlt : 2 ^ K + j < n) :
    let wm := toMont
      ((powModU64 primRoot ((mod64 - 1) / (2 ^ (K + 1) : ℕ).toUInt64) mod64).toUInt32)
    let vr := rootsInner wm ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat
        (((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat - 1) 0
        (v.set ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat montR1 h_half)
    let res := ensureRoots.outer n vr ((2 ^ (K + 2) : ℕ).toUInt64) hN f
    (res[2 ^ K + j]'hlt).toNat =
      ((primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1))) % mod64.toNat) ^ j *
        montR1.toNat % mod64.toNat := by
  -- unfold let wm, vr, res so we can work with the concrete terms
  simp only
  have h_halfLen : ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat = 2 ^ K :=
    pow2_toUInt64_halfLen K hK63
  have hlen_toNat : ((2 ^ (K + 1) : ℕ).toUInt64).toNat = 2 ^ (K + 1) :=
    nat_toUInt64_faithful _ (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have he_toNat : ((mod64 - 1) / (2 ^ (K + 1) : ℕ).toUInt64).toNat =
      (mod64.toNat - 1) / 2 ^ (K + 1) := by
    rw [UInt64.toNat_div, show (mod64 - 1).toNat = mod64.toNat - 1 from by decide, hlen_toNat]
  have hpow_val : (powModU64 primRoot ((mod64 - 1) / (2 ^ (K + 1) : ℕ).toUInt64) mod64).toNat =
      primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1)) % mod64.toNat :=
    (powmod_spec _ _ _ (by decide) (by decide)).trans (by rw [he_toNat])
  have hpow_lt :
      (powModU64 primRoot ((mod64 - 1) / (2 ^ (K + 1) : ℕ).toUInt64) mod64).toNat < 2 ^ 32 := by
    rw [hpow_val]; exact (Nat.mod_lt _ (by decide)).trans (by decide)
  have hpow_u32 :
      (powModU64 primRoot ((mod64 - 1) / (2 ^ (K + 1) : ℕ).toUInt64) mod64).toUInt32.toNat =
      primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1)) % mod64.toNat :=
    (UInt64_toUInt32_toNat _ hpow_lt).trans hpow_val
  have hw_lt : primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1)) % mod64.toNat < mod32.toNat := by
    rw [← mod32_eq_mod]; exact Nat.mod_lt _ (by decide)
  have hwm :
      (toMont ((powModU64 primRoot
          ((mod64 - 1) / (2 ^ (K + 1) : ℕ).toUInt64) mod64).toUInt32)).toNat =
      primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1)) % mod64.toNat *
        montR1.toNat % mod32.toNat := by
    rw [to_mont_nat _ (hpow_u32 ▸ hw_lt), hpow_u32]
  let wm := toMont ((powModU64 primRoot ((mod64 - 1) / (2 ^ (K + 1) : ℕ).toUInt64) mod64).toUInt32)
  let v' := v.set ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat montR1 h_half
  let inner_v := rootsInner wm ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat
      (((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat - 1) 0 v'
  rw [outer_preserves_target n hN inner_v (K + 1) f K j (by omega) hj hlt (by omega)]
  have h_inner_bound : ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat +
      (((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat - 1) < n := by
    rw [h_halfLen]
    have h2K := Nat.two_pow_pos K
    have h2K1 : 2 ^ (K + 1) = 2 ^ K + 2 ^ K := by ring
    omega
  have hrmp := rootsInner_montPow wm ((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat
      (((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat - 1) j v' (by rw [h_halfLen]; omega) h_inner_bound
  rw [show inner_v[2 ^ K + j]'hlt = inner_v[((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat + j]'(by omega)
      from by congr 1; omega]
  rw [hrmp]
  rw [show v'[((2 ^ (K + 1) : ℕ).toUInt64 / 2).toNat]'h_half = montR1 from by
        simp only [Nat.toUInt64_eq, UInt64.toNat_div, UInt64.toNat_ofNat', Nat.reducePow,
          UInt64.reduceToNat, Vector.getElem_set_self, v']]
  rw [montPow_spec wm _ j hwm, ← mod32_eq_mod]


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
    simp_all only [powModAuxU64, Nat.lt_one_iff, pow_zero, mul_one];
    rw [ Nat.mod_eq_of_lt hr ];
  | succ f ih =>
    unfold powModAuxU64
    norm_num at hmod_small
    simp only [beq_iff_eq, bne_iff_ne, pow_succ'] at *
    split_ifs
    · simp_all only [pow_zero, mul_one, Nat.mod_eq_of_lt hr, UInt64.toNat_zero]
    · rw [ ih ];
      · rw [ show e.toNat = 2 * ( e >>> 1 |> UInt64.toNat ) + 1 from ?_ ];
        · norm_num [
              ← ZMod.natCast_eq_natCast_iff',
              Nat.mod_eq_of_lt ( show b.toNat < 18446744073709551616 from by linarith ),
              Nat.mod_eq_of_lt ( show r.toNat < 18446744073709551616 from by linarith ) ];
          ring_nf;
          norm_num [ pow_mul', ← ZMod.natCast_eq_natCast_iff' ];
          norm_num [
            Nat.mod_eq_of_lt ( show r.toNat * b.toNat < 18446744073709551616 from by nlinarith ),
            Nat.mod_eq_of_lt ( show b.toNat ^ 2 < 18446744073709551616 from by nlinarith ) ];
        · cases Nat.mod_two_eq_zero_or_one e.toNat <;>
              simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
                         show (1 : UInt64).toNat % 64 = 1 from by decide] at *;
          · cases e ; simp_all only [UInt64.toNat_ofBitVec];
            rename_i k hk₁ hk₂ hk₃;
            contrapose! hk₂;
            ext
            simp [ hk₃ ];
          · omega;
      · -- By definition of modulo, the result of any number modulo mod_ is always less than mod_.
        have h_mod : ∀ (n : UInt64), (n % mod_).toNat < mod_.toNat := by
          intro n; exact (by
          convert Nat.mod_lt _ ( pos_of_gt hmod ) using 1);
        exact h_mod _;
      · simp only [UInt64.toNat_mod, UInt64.toNat_mul, Nat.reducePow];
        exact Nat.mod_lt _ ( by linarith );
      · simp_all [ Nat.shiftRight_eq_div_pow ];
        omega;
    · simp only [not_ne_iff] at *
      convert ih ( b * b % mod_ ) ( e >>> 1 ) r _ _ _ using 1;
      · rw [ show e.toNat = 2 * ( e.toNat / 2 ) by
              rw [ Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero _ ) ];
              rw [ ← Nat.even_iff ];
              rw [ Nat.even_iff ] ;
              replace := congr_arg ( fun x : UInt64 => x.toNat ) ‹e &&& 1 = 0› ;
              norm_num [ Nat.and_comm ] at this ⊢ ; aesop; ] ;
            norm_num [ pow_mul, Nat.mul_mod, Nat.pow_mod ];
        norm_num [ ← Nat.mul_mod, ← Nat.pow_mod ];
        rw [ ← sq ];
        rw [ Nat.mod_eq_of_lt ( show b.toNat ^ 2 < 18446744073709551616 from by nlinarith ) ] ; rfl;
      · exact Nat.mod_lt _ ( by positivity );
      · assumption;
      · convert Nat.div_lt_of_lt_mul <| show e.toNat < 2 * 2 ^ f from hf using 1

/-
`powModU64 base exp mod_` correctly computes `base^exp % mod_` when mod_ ≤ 2^32.
-/
lemma powmod_correct (base exp mod_ : UInt64)
    (hmod : 1 < mod_.toNat) (hmod_small : mod_.toNat ≤ 2 ^ 32) :
    (powModU64 base exp mod_).toNat = base.toNat ^ exp.toNat % mod_.toNat := by
  unfold powModU64;
  rw [ powmodAux_correct ];
  any_goals assumption;
  · simp [ ← ZMod.natCast_eq_natCast_iff', Nat.cast_pow ];
  · exact Nat.mod_lt _ ( pos_of_gt hmod );
  · exact exp.toNat_lt

/-
`toMont a` produces `(a.toNat * montR1.toNat) % mod32.toNat` when `a < mod32`.
-/
lemma to_mont_mont_r1 (a : UInt32) (ha : a.toNat < mod32.toNat) :
    (toMont a).toNat = (a.toNat * montR1.toNat) % mod32.toNat := by
  convert mont_mul_eq_nat a montR2 ha ( by decide ) using 1
  generalize_proofs at *;
  unfold montMulNat; norm_num [ MONT_PPRIME_spec, MONT_R2_spec, MONT_R1_spec ] ;
  norm_num [ show mod64.toNat = 3 * 2 ^ 30 + 1 by rfl, show montPprime.toNat = 3221225471 by rfl ];
  rw [ show mod32.toNat = 3221225473 by rfl ] ; omega;

/-
The twiddle factor `wm` used in `ensureRoots.outer` satisfies the `montPow_spec` hypothesis.
-/
lemma wm_spec (K : ℕ) (hK : K < 63) (n : ℕ) (hlen : 2 ^ (K + 1) ≤ n) :
    let len := (2 ^ (K + 1) : ℕ).toUInt64
    let wm := toMont ((powModU64 primRoot ((mod64 - 1) / len) mod64).toUInt32)
    let w := primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1)) % mod64.toNat
    wm.toNat = (w * montR1.toNat) % mod32.toNat := by
  convert to_mont_mont_r1 _ _;
  · convert powmod_correct _ _ _ _ _ |> Eq.symm using 2;
    rotate_left;
    rotate_left;
    · exact primRoot;
    · exact ( mod64 - 1 ) / ( 2 ^ ( K + 1 ) |> Nat.toUInt64 );
    · decide;
    · decide;
    · interval_cases K <;> congr 1;
    · have h_mod_lt :
          (powModU64 primRoot ((mod64 - 1) / (2 ^ (K + 1)).toUInt64) mod64).toNat < 2 ^ 32 := by
        have h_mod_lt :
            (powModU64 primRoot ((mod64 - 1) / (2 ^ (K + 1)).toUInt64) mod64).toNat <
            mod64.toNat := by
          convert powmod_correct primRoot ((mod64 - 1) / (2 ^ (K + 1)).toUInt64) mod64 _ _
              |> fun h => h.symm ▸ Nat.mod_lt _ ( by decide ) using 1 <;>
          decide;
        exact h_mod_lt.trans_le ( by decide );
      exact Nat.mod_eq_of_lt h_mod_lt;
  · interval_cases K <;> decide

/-
Generalized loop invariant for `ensureRoots.outer`:
When started from vector `v`, current `len`, and fuel `f`,
position `2^K + j` gets the correct root value, provided:
- `2^(s+1) = len` (current len is `2^(s+1)` with `s ≤ K`)
- `K - s < f` (enough fuel to reach level K)
- `2^(K+1) ≤ n` (level K fits in the vector)
- positions below `2^s` in `v` may contain anything
-/
lemma ensure_roots_outer_inv (n : ℕ) (hN : 0 < n)
    (v : Vector UInt32 n) (s f K j : ℕ)
    (hlen_K : 2 ^ (K + 1) ≤ n) (hj : j < 2 ^ K)
    (hsK : s ≤ K) (hf : K < s + f)
    (hK63 : K < 63)
    :
    let w := (primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1))) % mod64.toNat
    have hlt : 2 ^ K + j < n := by nlinarith [pow_succ 2 K]
    ((ensureRoots.outer n v ((2 ^ (s + 1) : ℕ).toUInt64) hN f)[2 ^ K + j]'hlt).toNat =
      (w ^ j * montR1.toNat) % mod64.toNat := by
  simp only
  induction f generalizing v s with
  | zero => omega
  | succ f ih =>
    by_cases hsk : s = K
    · -- Base case: s = K. subst eliminates K, replacing it with s throughout.
      subst hsk
      -- After subst: hlen_K : 2^(s+1) ≤ n.toNat, hj : j < 2^s, goal uses s not K.
      have hs63 : s < 63 := by omega
      have h_half : ((2 ^ (s + 1) : ℕ).toUInt64 / 2).toNat < n := by
        rw [pow2_toUInt64_halfLen s hs63]; nlinarith [Nat.two_pow_pos s, pow_succ 2 s]
      have hlt : 2 ^ s + j < n := by nlinarith [pow_succ 2 s]
      unfold ensureRoots.outer
      split_ifs with h_gt
      · exact absurd h_gt (pow2_toUInt64_le_nat s n (by omega) hlen_K)
      · simp only [pow2_toUInt64_shift s hs63]
        exact ensure_roots_base_case n hN v s j f hlen_K hj hs63 h_half hlt
    · -- Inductive case: s < K, so the outer step at level s does not affect 2^K+j.
      -- Unfold one step, rewrite len <<< 1 to 2^(s+2), apply IH with s+1.
      have hs_lt : s < K := Nat.lt_of_le_of_ne hsK hsk
      have hs63 : s < 63 := by omega
      have h_sn : 2 ^ (s + 1) ≤ n :=
        Nat.le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hlen_K
      unfold ensureRoots.outer
      split_ifs with h_gt
      · exact absurd h_gt (pow2_toUInt64_le_nat s n (by omega) h_sn)
      · simp only [pow2_toUInt64_shift s hs63]
        exact ih _ (s + 1) (by omega) (by omega)

/-
The `ensureRoots.outer` loop, started from an all-zero vector with `len = 2` and
64 fuel steps, places `(w ^ j * montR1.toNat) % mod64` at position `2^K + j`
(for `2^(K+1) ≤ n` and `j < 2^K`), where `w = primRoot ^ ((mod64−1) / 2^(K+1)) % mod64`.
-/
lemma ensure_roots_outer_geom (n : ℕ) (hN : 0 < n)
    (K j : ℕ) (hK63 : K < 63) (hlen : 2 ^ (K + 1) ≤ n) (hj : j < 2 ^ K) :
    let w := (primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (K + 1))) % mod64.toNat
    have hlt : 2 ^ K + j < n := by nlinarith [pow_succ 2 K]
    ((ensureRoots.outer n (Vector.replicate n (0 : UInt32)) 2 hN 64)[2 ^ K + j]).toNat =
      (w ^ j * montR1.toNat) % mod64.toNat := by
  have h2 : 2 ^ (0 + 1) ≤ n := by
    simp only [zero_add, pow_one]
    exact le_trans (Nat.le_of_dvd (by omega) ⟨ 2^K, by ring ⟩) hlen
  exact ensure_roots_outer_inv n hN _ 0 64 K j hlen hj (by omega) (by omega) hK63

theorem ensure_roots_spec (n : ℕ) (k j : ℕ)
    (hk63 : k < 63) (hlen_le : 2 ^ (k + 1) ≤ n) (hj : j < 2 ^ k) :
    let w := (primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (k + 1))) % mod64.toNat
    have : 2 ^ k + j < n := by nlinarith [pow_succ 2 k]
    (ensureRoots n)[2 ^ k + j] |>.toNat = (w ^ j * montR1.toNat) % mod64.toNat := by
  simp only
  have hn0' : n ≠ 0 := by
    have hpos : 0 < 2 ^ (k + 1) := by positivity
    omega
  -- `this : 2^k+j < n.toNat` is in scope from the `have` in the theorem statement.
  -- Universally quantify over the positivity proof to avoid proof-irrelevance issues.
  suffices h : ∀ (hN : 0 < n),
      let w := (primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (k + 1))) % mod64.toNat
      have hlt : 2 ^ k + j < n := by nlinarith [pow_succ 2 k]
      ((ensureRoots.outer n (Vector.replicate n (0 : UInt32)) 2 hN 64)[2 ^ k + j]).toNat =
        (w ^ j * montR1.toNat) % mod64.toNat by
    simp only [ensureRoots, dif_neg hn0']
    exact h _
  intro hN
  exact ensure_roots_outer_geom n hN k j hk63 hlen_le hj

/-!
#  ── Bit-reversal
-/

/-  `addMod32` and `subMod32` preserve the `< mod32` bound. -/
theorem addmod32_lt (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    (addMod32 a b).toNat < mod32.toNat := by
  rw [addmod32_correct a b ha hb]; exact Nat.mod_lt _ (by decide)

theorem submod32_lt (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    (subMod32 a b).toNat < mod32.toNat := by
  rw [submod32_correct a b ha hb]; exact Nat.mod_lt _ (by decide)

/-  `toMont` preserves `< mod32` when the input is bounded. -/
theorem to_mont_lt (a : UInt32) (ha : a.toNat < mod32.toNat) :
    (toMont a).toNat < mod32.toNat := (to_mont_correct a ha).1

/-
Generalized u-bound: when a < mod64 and b < 2^32 (any UInt32).
-/
theorem mont_mul_nat_u_bound_left (a b : ℕ)
    (ha : a < mod32.toNat) (hb : b < 2 ^ 32) :
    let T := a * b
    let m := (T % 2 ^ 32 * montPprime.toNat) % 2 ^ 32
    (T + m * mod64.toNat) / 2 ^ 32 < 2 * mod64.toNat := by
      have h_bound : a * b < mod64.toNat * 2 ^ 32 := by
        gcongr;
        exact ha;
      exact Nat.div_lt_of_lt_mul <| by
        nlinarith [
          show ( a * b % 2 ^ 32 * montPprime.toNat % 2 ^ 32 ) < 2 ^ 32 by
            exact Nat.mod_lt _ ( by decide ),
          show mod64.toNat = 3221225473 by rfl ] ;

/-
UInt64 product doesn't overflow when a < mod32 and b is any UInt32.
-/
theorem mont_T_toNat_left (a b : UInt32)
    (ha : a.toNat < mod32.toNat) :
    (a.toUInt64 * b.toUInt64).toNat = a.toNat * b.toNat := by
      norm_num [ UInt64.toNat_mul ];
      have ha32 : a.toNat ≤ 4294967295 :=
        Nat.le_of_lt_succ (lt_of_lt_of_le ha (by decide))
      have hb32 : b.toNat ≤ 4294967295 :=
        Nat.le_of_lt_succ (lt_of_lt_of_le b.toNat_lt (by decide))
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ ha32) (by linarith [hb32])

/-
Step 4 (left-bounded): u = (a*b + m*mod64) / 2^32 when only a < mod32.
-/
theorem mont_u_toNat_left (a b : UInt32)
    (ha : a.toNat < mod32.toNat) :
    let T := a.toUInt64 * b.toUInt64
    let m := T.toUInt32 * montPprime
    let mp := m.toUInt64 * mod64
    let lo := T.toUInt32.toUInt64 + mp.toUInt32.toUInt64
    let u := (T >>> 32) + (mp >>> 32) + (lo >>> 32)
    u.toNat = (a.toNat * b.toNat + m.toNat * mod64.toNat) / 2^32 := by
      have h_div_add_carry : ∀ (T_nat mp_nat : ℕ),
          T_nat < 2^64 → mp_nat < 2^64 →
          T_nat / 2^32 + mp_nat / 2^32 + (T_nat % 2^32 + mp_nat % 2^32) / 2^32 =
          (T_nat + mp_nat) / 2^32 := by omega;
      convert h_div_add_carry _ _ _ _ using 1;
      · simp +zetaDelta only [
            UInt64.toUInt32_mul, UInt32.toUInt32_toUInt64, UInt32.toUInt64_mul,
            UInt64.toUInt64_toUInt32, UInt64.toNat_add, UInt64.toNat_shiftRight,
            UInt64.toNat_mul, UInt32.toNat_toUInt64, Nat.reducePow, UInt64.reduceToNat,
            Nat.reduceMod, UInt64.toNat_mod, Nat.reduceDvd, Nat.mod_mod_of_dvd,
            Nat.mod_mul_mod, dvd_refl, Nat.mul_mod_mod, Nat.mod_add_mod,
            UInt32.toNat_mul] at *;
        rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ];
        · omega;
        · exact lt_of_le_of_lt
              ( Nat.mul_le_mul_right _ ( Nat.le_of_lt_succ ( Nat.mod_lt _ ( by decide ) ) ) )
              ( by decide );
        · have ha32 : a.toNat ≤ 4294967295 :=
            Nat.le_of_lt_succ (by linarith [ show mod32.toNat = 3221225473 by rfl ])
          have hb32 : b.toNat ≤ 4294967295 :=
            Nat.le_of_lt_succ (by linarith [ show b.toNat < 2^32 by exact b.toNat_lt ])
          exact lt_of_le_of_lt (Nat.mul_le_mul_right _ ha32) (by linarith [hb32]);
        · omega;
      · have ha32 : a.toNat < 2 ^ 32 := lt_of_lt_of_le ha (by decide)
        exact lt_of_le_of_lt
              ( Nat.mul_le_mul_left _ ( Nat.le_of_lt_succ ( show b.toNat < 2 ^ 32 from
                  b.toNat_lt ) ) )
              ( by linarith [ ha32 ] );
      · exact lt_of_lt_of_le
            ( Nat.mul_lt_mul_of_pos_right ( UInt32.toNat_lt _ ) ( by decide ) )
            ( by decide )

/-
The UInt32 montMul equals montMulNat on toNat (left-bounded version).
-/
theorem mont_mul_eq_nat_left (a b : UInt32)
    (ha : a.toNat < mod32.toNat) :
    (montMul a b).toNat = montMulNat a.toNat b.toNat := by
      unfold montMulNat;
      rw [ montMul ];
      have h_mod : ∀ (x : UInt64), x.toNat < 2 * mod64.toNat →
          (if x ≥ mod64 then (x - mod64).toUInt32 else x.toUInt32).toNat =
          x.toNat % mod64.toNat := by
        intros x hx
        by_cases h : x ≥ mod64;
        · simp only [ge_iff_le, h, ite_true]
          have hmod : mod64.toNat = 3221225473 := rfl
          have hh : mod64.toNat ≤ x.toNat := UInt64.le_iff_toNat_le.mp h
          have hx64 := x.toNat_lt
          simp only [UInt64.toNat_toUInt32, UInt64.toNat_sub]
          rw [show 2 ^ 64 - mod64.toNat + x.toNat = x.toNat - mod64.toNat + 2 ^ 64 from by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_sub_mod hh]
          rw [Nat.mod_eq_of_lt (by omega : x.toNat - mod64.toNat < mod64.toNat)]
          rw [Nat.mod_eq_of_lt (by omega)];
        · rw [ if_neg h, Nat.mod_eq_of_lt ];
          · exact Nat.mod_eq_of_lt ( show x.toNat < 2 ^ 32 from
                lt_of_lt_of_le ( show x.toNat < mod64.toNat from lt_of_not_ge h )
                ( by decide ) );
          · exact lt_of_not_ge h;
      rw [ h_mod ];
      · rw [ mont_u_toNat_left _ _ ha ];
        rw [ mont_m_toNat a b ];
      · rw [ mont_u_toNat_left a b ha ];
        rw [ mont_m_toNat a b ];
        exact mont_mul_nat_u_bound_left _ _ ha ( by exact b.toNat_lt )

/-  `montMul a b < mod32` whenever the **left** argument `a` is bounded.
    Proof: the intermediate value `u` satisfies `u < 2 * mod64`, so the
    conditional subtraction leaves the result in `[0, mod64)`. -/
theorem mont_mul_lt_of_left (a b : UInt32) (ha : a.toNat < mod32.toNat) :
    (montMul a b).toNat < mod32.toNat := by
  rw [mont_mul_eq_nat_left a b ha]
  exact mont_mul_nat_bound a.toNat b.toNat

/-
`montMul` is commutative since it only depends on the product a*b.
-/
theorem mont_mul_comm (a b : UInt32) : montMul a b = montMul b a := by
  -- Since multiplication is commutative for UInt64, the entire montMul function is commutative.
  have h_comm : a.toUInt64 * b.toUInt64 = b.toUInt64 * a.toUInt64 := by
    exact mul_comm _ _;
  unfold montMul; simp [ h_comm ] ;

/-  `montMul a b < mod32` whenever the **right** argument `b` is bounded. -/
theorem mont_mul_lt_of_right (a b : UInt32) (hb : b.toNat < mod32.toNat) :
    (montMul a b).toNat < mod32.toNat := by
  rw [mont_mul_comm]; exact mont_mul_lt_of_left b a hb

/-
Helper: `bitRevLoop` is a pure permutation and preserves the element bound.
-/
theorem bitRevLoop_bound {n : ℕ} (k i : ℕ)
    (v : Vector UInt32 n) (j : ℕ) (hv : v.all (· < mod32)) :
    (bitRevLoop k i v j).all (· < mod32) := by
      have h_bitRevLoop :
          ∀ (k : ℕ) (i : ℕ) (v : Vector UInt32 n) (j : ℕ),
          v.all (fun x => decide (x < mod32)) = true →
          (bitRevLoop k i v j).all (fun x => decide (x < mod32)) = true := by
        intro k i v j hv;
        induction k generalizing i v j with
        | zero => unfold bitRevLoop; simp_all [ Vector.all_eq_true ]
        | succ k ih =>
          unfold bitRevLoop; simp only [Vector.all_eq_true, decide_eq_true_eq] at *;
          convert ih ( i + 1 ) _ _ _ using 1
          generalize_proofs at *; (
          intro i hi; split_ifs <;> simp_all only [Vector.getElem_set] ;
          · split_ifs <;> simp_all [ Vector.get ];
          · split_ifs <;> simp_all +decide;
          · split_ifs <;> simp_all +decide)
      generalize_proofs at *; (
      exact h_bitRevLoop k i v j hv)

/-
Setting one element of a bounded vector to a bounded value preserves the all-bound.
-/
theorem vector_all_lt_set {n : ℕ} (v : Vector UInt32 n) (i : ℕ) (h : i < n)
    (x : UInt32) (hv : v.all (· < mod32)) (hx : x.toNat < mod32.toNat) :
    (v.set i x h).all (· < mod32) := by
  simp_all only [Vector.set]
  simp_all only [Vector.all_eq_true, decide_eq_true_eq,
                Array.all_eq_true', Array.toList_set, Array.mem_def, Vector.all_mk]
  intro y hy; rw [ List.mem_iff_get ] at hy; obtain ⟨ j, hj ⟩ := hy;
  by_cases hi : j = ⟨i, by aesop⟩ <;>
    simp_all only [List.get_eq_getElem, List.getElem_set, if_true]
  · exact hx
  · grind

/-  Helper: `radix2Pass` applies `addMod32`/`subMod32` in-place and preserves the bound. -/
theorem radix2Pass_bound {n : ℕ} (k i : ℕ) (v : Vector UInt32 n)
    (hv : v.all (· < mod32)) :
    (radix2Pass k i v).all (· < mod32) := by
  induction k generalizing i v with
  | zero => exact hv
  | succ k ih =>
    simp only [radix2Pass]
    apply ih
    split_ifs with h1 h2
    · -- Positions lo = 2*i and hi = 2*i+1 are both in bounds; apply addMod32 then subMod32.
      have helo : (v.get ⟨2 * i, h1⟩).toNat < mod32.toNat := by
        have := (Vector.all_eq_true.mp hv) (2 * i) h1
        simpa [decide_eq_true_eq, UInt32.lt_iff_toNat_lt] using this
      have hehi : (v.get ⟨2 * i + 1, h2⟩).toNat < mod32.toNat := by
        have := (Vector.all_eq_true.mp hv) (2 * i + 1) h2
        simpa [decide_eq_true_eq, UInt32.lt_iff_toNat_lt] using this
      have hv1 : (v.set (2 * i) (addMod32 (v.get ⟨2 * i, h1⟩) (v.get ⟨2 * i + 1, h2⟩)) h1).all
          (· < mod32) :=
        vector_all_lt_set _ _ _ _ hv (addmod32_lt _ _ helo hehi)
      exact vector_all_lt_set _ _ _ _ hv1 (submod32_lt _ _ helo hehi)
    · exact hv
    · exact hv

/-  Helper: one pass of the outer radix-4 loop preserves the element bound.
    Each butterfly uses `addMod32`, `subMod32`, and `montMul` with the left
    argument taken from the data vector (bounded), so all outputs are < mod32. -/
/- Conditional set preserves bound. -/
theorem vector_all_lt_dite_set {n : ℕ} (v : Vector UInt32 n)
    (idx : ℕ) (x : UInt32) (hv : v.all (· < mod32))
    (hx : x.toNat < mod32.toNat) :
    (if h : idx < n then v.set idx x h else v).all (· < mod32) := by
  split_ifs with h
  · exact vector_all_lt_set _ _ _ _ hv hx
  · exact hv

/-
Getting an element from a bounded vector gives a bounded value, or 0 (which is bounded).
-/
theorem vector_get_lt_of_all {n : ℕ} (v : Vector UInt32 n)
    (idx : ℕ) (hv : v.all (· < mod32)) :
    (if h' : idx < n then v.get ⟨idx, h'⟩ else 0).toNat < mod32.toNat := by
  split_ifs with h'
  · exact UInt32.lt_iff_toNat_lt.mp (by simpa using (Vector.all_eq_true.mp hv) _ h')
  · exact by decide

theorem butterfly4_bound {n : ℕ}
    (a : Vector UInt32 n) (inverse : Bool) (roots : Vector UInt32 n)
    (s len i2 j2 : ℕ) (hv : a.all (· < mod32)) :
    (butterfly4 a inverse roots s len i2 j2).all (· < mod32) := by
      apply vector_all_lt_dite_set;
      · apply vector_all_lt_dite_set;
        · apply vector_all_lt_dite_set;
          · apply vector_all_lt_dite_set;
            · exact hv;
            · apply addmod32_lt;
              · apply addmod32_lt;
                · exact vector_get_lt_of_all a (i2 + j2) hv;
                · apply mont_mul_lt_of_left;
                  exact vector_get_lt_of_all a (i2 + j2 + s) hv;
              · apply mont_mul_lt_of_right;
                apply addmod32_lt;
                · exact vector_get_lt_of_all a (i2 + len + j2) hv;
                · apply mont_mul_lt_of_left;
                  apply vector_get_lt_of_all; assumption;
          · apply submod32_lt;
            · apply addmod32_lt;
              · exact vector_get_lt_of_all a (i2 + j2) hv;
              · apply mont_mul_lt_of_left;
                exact vector_get_lt_of_all a (i2 + j2 + s) hv;
            · apply mont_mul_lt_of_right;
              apply addmod32_lt;
              · exact vector_get_lt_of_all a (i2 + len + j2) hv;
              · apply mont_mul_lt_of_left;
                apply vector_get_lt_of_all; assumption;
        · apply addmod32_lt
          · apply submod32_lt
            · apply vector_get_lt_of_all; assumption
            · apply mont_mul_lt_of_left; apply vector_get_lt_of_all; assumption
          · exact mont_mul_lt_of_right _ _ ( submod32_lt _ _ ( by
              exact vector_get_lt_of_all a (i2 + len + j2) hv ) ( by
              apply mont_mul_lt_of_left;
              apply vector_get_lt_of_all; assumption ) )
      · apply submod32_lt;
        · apply submod32_lt;
          · exact vector_get_lt_of_all a (i2 + j2) hv;
          · apply mont_mul_lt_of_left;
            exact vector_get_lt_of_all a (i2 + j2 + s) hv;
        · exact mont_mul_lt_of_right _ _ ( submod32_lt _ _ ( by
            exact vector_get_lt_of_all a (i2 + len + j2) hv ) ( by
            apply mont_mul_lt_of_left;
            apply vector_get_lt_of_all; assumption ) )

theorem radix4Inner_bound {n : ℕ}
    (inverse : Bool) (roots : Vector UInt32 n) (s len i2 : ℕ)
    (k j2 : ℕ) (v : Vector UInt32 n) (hv : v.all (· < mod32)) :
    (radix4Inner inverse roots s len i2 k j2 v).all (· < mod32) := by
      induction k generalizing j2 v with
      | zero => exact hv
      | succ k ih => exact ih _ _ ( butterfly4_bound _ _ _ _ _ _ _ hv )

theorem radix4Middle_bound {n : ℕ} (inverse : Bool) (roots : Vector UInt32 n)
    (s len : ℕ) (k b : ℕ) (v : Vector UInt32 n) (hv : v.all (· < mod32)) :
    (radix4Middle inverse roots s len k b v).all (· < mod32) := by
      convert hv using 1;
      induction k generalizing b v with
      | zero => rfl
      | succ k ih =>
        convert ih ( b + 1 ) _ _ using 1;
        · rw [ radix4Inner_bound inverse roots s len
            ( b * 2 * len ) s 0 v hv ];
          exact hv;
        · convert radix4Inner_bound inverse roots s len
            ( b * 2 * len ) s 0 v hv using 1

/-- All outputs of nttInplace are < mod32. -/
theorem ntt_inplace_output_bound {m : ℕ}
    (v : Vector UInt32 m) (inverse : Bool)
    (roots : Vector UInt32 m)
    (hv_bound : v.all (· < mod32)) :
    (nttInplace v inverse roots).all (· < mod32) := by
  unfold nttInplace
  -- Step 1: after the toMont map (forward) or identity (inverse), bound is preserved.
  have ha1 : (if !inverse then v.map toMont else v).all (· < mod32) := by
    split_ifs with h
    · rw [Vector.all_eq_true]
      intro i hi
      simp only [decide_eq_true_eq, Vector.getElem_map]
      have hvi : v[i].toNat < mod32.toNat := by
        have := (Vector.all_eq_true.mp hv_bound) i hi
        simp only [decide_eq_true_eq] at this
        exact UInt32.lt_iff_toNat_lt.mp this
      exact UInt32.lt_iff_toNat_lt.mpr (to_mont_lt v[i] hvi)
    · exact hv_bound
  set a1 := if !inverse then v.map toMont else v with ha1_def
  -- Step 2: bitRevLoop is a permutation; bound is preserved.
  have ha2 : (bitRevLoop (m - 1) 0 a1 0).all (· < mod32) :=
    bitRevLoop_bound _ _ _ _ ha1
  set a2 := bitRevLoop (m - 1) 0 a1 0 with ha2_def
  -- Step 3: the optional radix2Pass (and its identity alternative) preserves the bound.
  set k := nttInplace.go 64 m 0
  have ha3 : (if k &&& 1 != 0 then (radix2Pass (m / 2) 0 a2, (4 : UInt64))
              else (a2, (2 : UInt64))).1.all (· < mod32) := by
    split_ifs
    · exact radix2Pass_bound _ _ _ ha2
    · exact ha2
  set a3 := (if k &&& 1 != 0 then (radix2Pass (m / 2) 0 a2, (4 : UInt64))
             else (a2, (2 : UInt64))).1
  set start := (if k &&& 1 != 0 then (radix2Pass (m / 2) 0 a2, (4 : UInt64))
                else (a2, (2 : UInt64))).2
  -- Step 4: the outer radix-4 loop preserves the bound (proved by induction via helper).
  have ha4 : (nttInplace.outerLoop inverse roots a3 start 64).all (· < mod32) := by
    suffices h : ∀ (a : Vector UInt32 m) (len : UInt64) (fuel : ℕ),
        a.all (· < mod32) → (nttInplace.outerLoop inverse roots a len fuel).all (· < mod32) from
      h a3 start 64 ha3
    intro a len fuel ha
    induction fuel generalizing a len with
    | zero => simp [nttInplace.outerLoop, ha]
    | succ f ih =>
      simp only [nttInplace.outerLoop]
      split_ifs with hcond
      · exact ha
      · exact ih _ _ (radix4Middle_bound _ _ _ _ _ _ _ ha)
  set a4 := nttInplace.outerLoop inverse roots a3 start 64
  -- Step 5: the final inverse scaling (or identity) preserves the bound.
  split_ifs with hinv
  · rw [Vector.all_eq_true]
    intro i hi
    simp only [decide_eq_true_eq, Vector.getElem_map]
    have ha4i : a4[i].toNat < mod32.toNat := by
      have := (Vector.all_eq_true.mp ha4) i hi
      simp only [decide_eq_true_eq] at this
      exact UInt32.lt_iff_toNat_lt.mp this
    exact UInt32.lt_iff_toNat_lt.mpr (mont_mul_lt_of_left a4[i] _ ha4i)
  · exact ha4

/-!
#  ── NTT forward correctness ───────────────────────────────────────────────────

Helper lemmas decompose the proof by function:
  Level 1 – arithmetic primitives in ZMod
  Level 2 – root-table correctness (ensureRoots)
  Level 3 – algorithm permutation (bitRevLoop)
  Level 4 – full forward-NTT correctness given a correct root table
The main theorem follows from levels 2 + 4.
-/

instance : Fact (Nat.Prime mod32.toNat) := ⟨prime_3221225473⟩

private lemma two_ne_zero_ZMod : (2 : ZMod mod32.toNat) ≠ 0 := by decide

private lemma two_pow32_ne_zero_ZMod : (2 : ZMod mod32.toNat) ^ 32 ≠ 0 :=
  pow_ne_zero _ two_ne_zero_ZMod

private lemma prim_root_ne_zero_ZMod : (primRoot.toNat : ZMod mod32.toNat) ≠ 0 := by decide

private lemma mont_r1_ne_zero_ZMod : (montR1.toNat : ZMod mod32.toNat) ≠ 0 :=
  MONT_R1_ZMod ▸ two_pow32_ne_zero_ZMod

/-- `addMod32 a b` computes addition in `ZMod mod32.toNat`. -/
lemma addmod32_ZMod (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    ((addMod32 a b).toNat : ZMod mod32.toNat) =
      (a.toNat : ZMod mod32.toNat) + b.toNat := by
  rw [addmod32_correct a b ha hb, ZMod.natCast_mod, Nat.cast_add]

/-- `subMod32 a b` computes subtraction in `ZMod mod32.toNat`. -/
lemma submod32_ZMod (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    ((subMod32 a b).toNat : ZMod mod32.toNat) =
      (a.toNat : ZMod mod32.toNat) - b.toNat := by
  rw [submod32_correct a b ha hb, ZMod.natCast_mod]
  push_cast [show b.toNat ≤ a.toNat + mod32.toNat from by omega]
  simp

/-- `montMul a b` computes `a · b · R⁻¹ mod p` in `ZMod mod32.toNat`, where R = 2^32. -/
lemma mont_mul_ZMod (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    ((montMul a b).toNat : ZMod mod32.toNat) =
      (a.toNat : ZMod mod32.toNat) * b.toNat * (2 ^ 32 : ZMod mod32.toNat)⁻¹ := by
  have hcorr := (mont_mul_correct a b ha hb).2
  have h2_ne : (2 : ZMod mod32.toNat)^32 ≠ 0 := two_pow32_ne_zero_ZMod
  have h_zmod : ((montMul a b).toNat : ZMod mod32.toNat) * 2^32 =
      (a.toNat : ZMod mod32.toNat) * b.toNat := by
    have h := congr_arg (Nat.cast (R := ZMod mod32.toNat)) hcorr
    simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
    exact h
  apply mul_right_cancel₀ h2_ne
  rw [mul_assoc, inv_mul_cancel₀ h2_ne, mul_one]
  exact h_zmod

/-- `toMont a` maps `a` into the Montgomery domain: it computes `a · R mod p`
    in `ZMod mod32.toNat`, where R = 2^32 ≡ montR1 (mod p). -/
lemma to_mont_ZMod (a : UInt32) (ha : a.toNat < mod32.toNat) :
    ((toMont a).toNat : ZMod mod32.toNat) =
      (a.toNat : ZMod mod32.toNat) * (montR1.toNat : ZMod mod32.toNat) := by
  have hcorr := (to_mont_correct a ha).2
  have h2_ne : (2 : ZMod mod32.toNat)^32 ≠ 0 := two_pow32_ne_zero_ZMod
  have h_zmod : ((toMont a).toNat : ZMod mod32.toNat) * 2^32 =
      (a.toNat : ZMod mod32.toNat) * 2^64 := by
    have h := congr_arg (Nat.cast (R := ZMod mod32.toNat)) hcorr
    simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
    exact h
  have hMONT_R1 : (montR1.toNat : ZMod mod32.toNat) = 2^32 := by
    have : montR1.toNat = 2^32 % mod32.toNat := by decide
    rw [this, ZMod.natCast_mod]; norm_num
  rw [hMONT_R1]
  apply mul_right_cancel₀ h2_ne
  rw [h_zmod]; ring

/-- A root table is correct for an `m`-point NTT when every entry at index `len/2 + j`
    holds the twiddle factor `ω_{len}^j` in the Montgomery domain (multiplied by R),
    where `ω_{len} = primRoot ^ ((mod64 - 1) / len)` is a primitive `len`-th root of unity
    and R = montR1 = 2^32 mod mod64. -/
def ntt_roots_correct (m : ℕ) (roots : Vector UInt32 m) : Prop :=
  ∀ (len j : ℕ), 2 ≤ len → len ∣ m → j < len / 2 →
    (hbound : len / 2 + j < m) →
    ((roots[len / 2 + j]'hbound).toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j) *
      (montR1.toNat : ZMod mod32.toNat)

-- Divisors of 2^N that are ≥ 2 are themselves powers of 2 with exponent ≥ 1.
lemma pow2_dvd_is_pow2 (len N : ℕ) (hdvd : len ∣ 2 ^ N) (hlen : 2 ≤ len) :
    ∃ k : ℕ, len = 2 ^ (k+1) := by
  rw [Nat.dvd_prime_pow (by decide : Nat.Prime 2)] at hdvd
  obtain ⟨i, _, rfl⟩ := hdvd
  cases i with
  | zero => simp at hlen
  | succ i => exact ⟨i, rfl⟩

-- Cast of (w^j * montR1 % mod64) into ZMod equals primRoot^(e*j) * montR1.
lemma ensure_roots_zmod_cast (k j : ℕ) :
    let w := (primRoot.toNat ^ ((mod64.toNat - 1) / 2 ^ (k + 1))) % mod64.toNat
    ((w ^ j * montR1.toNat % mod64.toNat : ℕ) : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ (k + 1) * j) *
      (montR1.toNat : ZMod mod32.toNat) := by
  simp only
  rw [mod32_eq_mod, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow,
      ZMod.natCast_mod, Nat.cast_pow, ← pow_mul]

/-- `ensureRoots m` produces a correct NTT root table for an `m`-point NTT. -/
lemma ensure_roots_ntt_correct {m : ℕ}
    (hm_pow2 : Nat.isPowerOfTwo m)
    (hm_dvd : m ∣ mod64.toNat - 1)
    :
    ntt_roots_correct m (ensureRoots m) := by
  intro len j hlen hdvd hj hbound
  obtain ⟨N, hN⟩ := hm_pow2
  rw [hN] at hdvd
  obtain ⟨k, hlen_eq⟩ := pow2_dvd_is_pow2 len N hdvd hlen
  have hlend2 : len / 2 = 2^k := by omega
  have hle : 2^(k+1) ≤ m := by
    rw [hN]; exact Nat.le_of_dvd (Nat.two_pow_pos N) (hlen_eq ▸ hdvd)
  have hj' : j < 2^k := by rwa [hlend2] at hj
  -- Derive k < 63 from m ∣ mod64.toNat - 1 (so m ≤ mod64.toNat - 1 < 2^64)
  have hk63 : k < 63 := by
    have hm_le : m ≤ mod64.toNat - 1 := Nat.le_of_dvd (by decide) hm_dvd
    have hm_lt : m < 2^64 := Nat.lt_of_le_of_lt hm_le (by decide)
    have h2k_lt : 2^(k+1) < 2^64 := Nat.lt_of_le_of_lt hle hm_lt
    have h := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2k_lt
    omega
  have hspec := ensure_roots_spec m k j hk63 hle hj'
  simp only at hspec
  have hlt : 2^k + j < m := by nlinarith [Nat.two_pow_pos k]
  have h_idx : (ensureRoots m)[len / 2 + j]'hbound = (ensureRoots m)[2^k + j]'hlt := by
    congr 1; omega
  rw [h_idx, hspec, hlen_eq]
  exact ensure_roots_zmod_cast k j

/-
After `toMont`, each element is `v[j] * montR1` in ZMod.  Factoring montR1 out of
    the DFT sum gives the main theorem's right-hand side.
-/
lemma to_mont_dft_factor {m : ℕ}
    (v : Vector UInt32 m)
    (hv_bound : v.all (· < mod32))
    (ω : ZMod mod32.toNat) (k : ℕ) :
    ∑ j : Fin m,
      ((toMont (v[j.val])).toNat : ZMod mod32.toNat) * ω ^ (j.val * k) =
    (montR1.toNat : ZMod mod32.toNat) * ∑ j : Fin m,
      (v[j.val].toNat : ZMod mod32.toNat) * ω ^ (j.val * k) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi_bound : v[i.val].toNat < mod32.toNat := by
    simp only [Vector.all_eq_true] at hv_bound
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using hv_bound i.val i.isLt)
  rw [to_mont_ZMod _ hi_bound]; ring

/-
`radix2Pass` does not modify elements outside the range `[2*i, 2*(i+k)-1]`.
-/
lemma radix2Pass_preserves {n : ℕ} (k i : ℕ)
    (a : Vector UInt32 n) (idx : ℕ) (hidx : idx < n)
    (h_below : idx < 2 * i ∨ idx ≥ 2 * (i + k)) :
    (radix2Pass k i a).get ⟨idx, hidx⟩ = a.get ⟨idx, hidx⟩ := by
  cases h_below <;> simp_all only [Vector.get_eq_getElem];
  · induction k generalizing i a with
    | zero => rfl
    | succ k ih =>
      unfold radix2Pass;
      grind;
  · -- By induction on $k$: elements outside the range $[2i, 2(i+k)-1]$ remain unchanged.
    induction k generalizing i a idx with
    | zero => rfl
    | succ k ih =>
      unfold radix2Pass; simp +decide [ * ] ;
      grind

/-
Correctness of `radix2Pass`: after processing `n/2` pairs starting from index 0,
    each pair is replaced by its sum and difference in ZMod arithmetic.
    Specifically, for each pair index `p < n/2`:
    - result[2p] = a[2p] + a[2p+1]  (mod mod32)
    - result[2p+1] = a[2p] - a[2p+1] (mod mod32)

After `radix2Pass`, the value at position `2*p` for pair `p` equals
    `addMod32(original[2p], original[2p+1])`.
-/
lemma radix2Pass_get_lo {n : ℕ} (k i : ℕ)
    (a : Vector UInt32 n) (p : ℕ)
    (hp : 2 * p + 1 < n) (hpi : i ≤ p) (hpk : p < i + k) (hk : i + k ≤ n / 2) :
    (radix2Pass k i a).get ⟨2 * p, by omega⟩ =
      addMod32 (a.get ⟨2 * p, by omega⟩) (a.get ⟨2 * p + 1, hp⟩) := by
  induction k generalizing i a p with
  | zero => linarith
  | succ k ih =>
    by_cases h : 2 * i < n ∧ 2 * i + 1 < n;
    · by_cases hpi' : i = p;
      · unfold radix2Pass;
        rw [ radix2Pass_preserves ];
        · split_ifs <;> simp_all +decide [ Vector.get ];
        · omega;
      · specialize ih ( i + 1 )
            ( if h1 : 2 * i < n then
                if h2 : 2 * i + 1 < n then
                  ( a.set ( 2 * i )
                    ( addMod32 ( a.get ⟨ 2 * i, h1 ⟩ )
                      ( a.get ⟨ 2 * i + 1, h2 ⟩ ) ) h1
                  ).set ( 2 * i + 1 )
                    ( subMod32 ( a.get ⟨ 2 * i, h1 ⟩ )
                      ( a.get ⟨ 2 * i + 1, h2 ⟩ ) ) h2
                else a else a )
            p hp ( by omega ) ( by omega ) ( by omega )
        simp_all +decide [ radix2Pass ];
        simp +decide [ Vector.get, Vector.set ];
        grind;
    · omega

/-
After `radix2Pass`, the value at position `2*p+1` for pair `p` equals
    `subMod32(original[2p], original[2p+1])`.
-/
lemma radix2Pass_get_hi {n : ℕ} (k i : ℕ)
    (a : Vector UInt32 n) (p : ℕ)
    (hp : 2 * p + 1 < n) (hpi : i ≤ p) (hpk : p < i + k) (hk : i + k ≤ n / 2) :
    (radix2Pass k i a).get ⟨2 * p + 1, hp⟩ =
      subMod32 (a.get ⟨2 * p, by omega⟩) (a.get ⟨2 * p + 1, hp⟩) := by
  induction k generalizing i a with
  | zero => linarith
  | succ k ih =>
    by_cases h : p = i;
    · rw [ radix2Pass ];
      split_ifs <;> simp_all only []
      · rw [ radix2Pass_preserves ];
        · simp +decide [ Vector.get ];
        · omega;
      · omega;
      · omega;
    · unfold radix2Pass; simp only [ * ];
      convert ih ( i + 1 ) _ _ _ _ using 1;
      · split_ifs <;> simp_all +decide [ Vector.get ];
        grind;
      · exact Nat.succ_le_of_lt ( lt_of_le_of_ne hpi ( Ne.symm h ) );
      · all_goals omega;
      · omega

/-
Correctness of `radix2Pass`: after processing `n/2` pairs starting from index 0,
    each pair is replaced by its sum and difference in ZMod arithmetic.
    Specifically, for each pair index `p < n/2`:
    - result[2p] = a[2p] + a[2p+1]  (mod mod32)
    - result[2p+1] = a[2p] - a[2p+1] (mod mod32)
-/
lemma radix2Pass_ZMod_pair {n : ℕ} (a : Vector UInt32 n)
    (ha : a.all (· < mod32)) (p : ℕ) (hp : 2 * p + 1 < n) :
    let result := radix2Pass (n / 2) 0 a
    ((result.get ⟨2 * p, by omega⟩).toNat : ZMod mod32.toNat) =
      ((a.get ⟨2 * p, by omega⟩).toNat : ZMod mod32.toNat) +
      (a.get ⟨2 * p + 1, hp⟩).toNat ∧
    ((result.get ⟨2 * p + 1, hp⟩).toNat : ZMod mod32.toNat) =
      ((a.get ⟨2 * p, by omega⟩).toNat : ZMod mod32.toNat) -
      (a.get ⟨2 * p + 1, hp⟩).toNat := by
  constructor;
  · rw [ radix2Pass_get_lo ];
    any_goals omega;
    apply addmod32_ZMod;
    · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      exact ha _ ( by linarith );
    · rw [ Vector.all_eq_true ] at ha;
      simpa using ha _ hp;
  · convert submod32_ZMod _ _ _ _ using 1;
    · convert congr_arg ( fun x : UInt32 => ( x.toNat : ZMod mod32.toNat ) )
          ( radix2Pass_get_hi ( n / 2 ) 0 a p hp ( by omega ) ( by omega ) ( by omega ) ) using 1;
    · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      exact ha _ ( by linarith );
    · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      exact ha _ hp

/-
  Level 3a – algebraic property of ω.
  ω = primRoot^((p-1)/m) satisfies ω^(m/2) = -1 in ZMod p whenever m = 2^n with n ≥ 1
  and m ∣ p - 1.  This is the hypothesis required by `ref_ntt_eq_dft`.
  Proof sketch: primRoot is a primitive root mod p (`prim_root_PRIM_ROOT`),
  so ω^(m/2) = primRoot^((p-1)/2) = -1 by Euler's criterion.
  Since m = 2^n we have m/2 = 2^(n-1).
-/
lemma ω_is_primitive_half {m : UInt64} (n : ℕ)
    (hm_eq : m.toNat = 2 ^ n) (hm_dvd : m.toNat ∣ mod64.toNat - 1) :
    let ω : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m.toNat)
    n = 0 ∨ ω ^ 2 ^ (n - 1) = -1 := by
  simp only
  rcases n with _ | n
  · left; rfl
  · right
    simp only [Nat.succ_sub_one]
    rw [← pow_mul]
    -- Arithmetic: (mod64-1)/m * 2^n = (mod64-1)/2, using m = 2^(n+1) ∣ mod64-1
    have hdvd : 2 ^ (n + 1) ∣ mod64.toNat - 1 := hm_eq ▸ hm_dvd
    have harith : (mod64.toNat - 1) / m.toNat * 2 ^ n = (mod64.toNat - 1) / 2 := by
      rw [hm_eq]
      obtain ⟨c, hc⟩ := hdvd
      have h1 : (mod64.toNat - 1) / 2 ^ (n + 1) = c :=
        hc ▸ Nat.mul_div_cancel_left c (by positivity)
      have h2 : (mod64.toNat - 1) / 2 = c * 2 ^ n := by
        rw [hc, show 2 ^ (n + 1) = 2 * 2 ^ n from by ring,
            show 2 * 2 ^ n * c = 2 * (c * 2 ^ n) from by ring,
            Nat.mul_div_cancel_left _ (by norm_num)]
      rw [h1, h2, mul_comm]
    rw [harith]
    exact prim_root_half_eq_neg_one

/-- Nat version of ω_is_primitive_half: works when m : ℕ instead of UInt64. -/
lemma ω_is_primitive_half_nat (m n : ℕ) (hm_eq : m = 2 ^ n) (hm_dvd : m ∣ mod64.toNat - 1) :
    n = 0 ∨
    ((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)) ^ 2 ^ (n - 1) = -1 := by
  have hn : n < 64 := by
    have hm_le : m ≤ mod64.toNat - 1 := Nat.le_of_dvd (by decide) hm_dvd
    have hm_lt : m < 2 ^ 64 := Nat.lt_of_le_of_lt hm_le (by decide)
    have h2n_lt : 2 ^ n < 2 ^ 64 := hm_eq ▸ hm_lt
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2n_lt
  have hm_small : m < 2 ^ 64 := hm_eq ▸ Nat.pow_lt_pow_right (by norm_num) hn
  have hm_toNat : m.toUInt64.toNat = m := nat_toUInt64_faithful m hm_small
  have h := ω_is_primitive_half (m := m.toUInt64) n
    (by rw [hm_toNat]; exact hm_eq)
    (by rw [hm_toNat]; exact hm_dvd)
  simp only at h
  rwa [hm_toNat] at h

-- Helper: look up a root value via ntt_roots_correct at an explicit index.
-- `heq` proves `idx = len / 2 + j`; after subst the goal is exactly `hroots`.
lemma ntt_roots_correct_at {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots)
    (len j idx : ℕ) (h2 : 2 ≤ len) (hdvd : len ∣ N) (hj : j < len / 2)
    (hidx : idx < N) (heq : idx = len / 2 + j) :
    ((roots[idx]'hidx).toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j) *
        (montR1.toNat : ZMod mod32.toNat) := by
  subst heq; exact hroots len j h2 hdvd hj hidx

-- Helper: montMul ZMod when the right factor equals τ * 2^32.
-- Cancels the Montgomery 2^32 factor: (montMul a t).toNat = a.toNat * τ in ZMod.
lemma mont_mul_zmod_right_twiddle (a t : UInt32) (τ : ZMod mod32.toNat)
    (ha : a.toNat < mod32.toNat) (ht : t.toNat < mod32.toNat)
    (ht_z : (t.toNat : ZMod mod32.toNat) = τ * 2 ^ 32) :
    ((montMul a t).toNat : ZMod mod32.toNat) = (a.toNat : ZMod mod32.toNat) * τ := by
  have h2ne : (2 : ZMod mod32.toNat) ^ 32 ≠ 0 := two_pow32_ne_zero_ZMod
  rw [mont_mul_ZMod _ _ ha ht, ht_z,
      show (a.toNat : ZMod mod32.toNat) * (τ * 2 ^ 32) * (2 ^ 32)⁻¹ =
           (a.toNat : ZMod mod32.toNat) * τ * (2 ^ 32 * (2 ^ 32)⁻¹) from by ring,
      mul_inv_cancel₀ h2ne, mul_one]

-- Helper: montMul ZMod when the left factor equals τ * 2^32.
-- Cancels the Montgomery 2^32 factor: (montMul a t).toNat = τ * t.toNat in ZMod.
lemma mont_mul_zmod_left_twiddle (a t : UInt32) (τ : ZMod mod32.toNat)
    (ha : a.toNat < mod32.toNat) (ht : t.toNat < mod32.toNat)
    (ha_z : (a.toNat : ZMod mod32.toNat) = τ * 2 ^ 32) :
    ((montMul a t).toNat : ZMod mod32.toNat) = τ * (t.toNat : ZMod mod32.toNat) := by
  have h2ne : (2 : ZMod mod32.toNat) ^ 32 ≠ 0 := two_pow32_ne_zero_ZMod
  rw [mont_mul_ZMod _ _ ha ht, ha_z,
      show (τ * 2 ^ 32) * (t.toNat : ZMod mod32.toNat) * (2 ^ 32)⁻¹ =
           τ * (t.toNat : ZMod mod32.toNat) * (2 ^ 32 * (2 ^ 32)⁻¹) from by ring,
      mul_inv_cancel₀ h2ne, mul_one]

-- Helper: Vector.getD idx 0 = Vector[idx]'h when idx < N.
lemma vector_getD_eq_getElem {α : Type*} {N : ℕ} (v : Vector α N)
    (idx : ℕ) (h : idx < N) (default : α) :
    v.getD idx default = v[idx]'h := by
  unfold Vector.getD
  have ha : idx < v.toArray.size := by rw [v.size_toArray]; exact h
  rw [← Array.getElem_eq_getD (fallback := default) (h := ha)]
  exact Vector.getElem_toArray ha

/-
  Level 3c – Structural lemmas: what `butterfly4` returns at each output position.
-/

-- Shared expansion: unfolds butterfly4 (forward) into the explicit Vector.set chain once,
-- absorbing the expensive simp only [butterfly4, ...] cost for all four getElem_posX lemmas.
private lemma butterfly4_forward_expand {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (ht1 : s + j2 < N) (ht2 : len + j2 < N) (ht3 : len + j2 + s < N) :
    butterfly4 a false roots s len i2 j2 =
      let t1 := roots[s + j2]'ht1
      let t2 := roots[len + j2]'ht2
      let t3 := roots[len + j2 + s]'ht3
      let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
      let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
      let P  := addMod32 (a[i2 + j2]'hbnd0) aB
      let Rv := addMod32 (a[i2 + len + j2]'hbnd2) aD
      let Q  := subMod32 (a[i2 + j2]'hbnd0) aB
      let Sv := subMod32 (a[i2 + len + j2]'hbnd2) aD
      let t2R := montMul t2 Rv
      let t3S := montMul t3 Sv
      ((((a.set (i2 + j2) (addMod32 P t2R) hbnd0).set
              (i2 + len + j2) (subMod32 P t2R) hbnd2).set
              (i2 + j2 + s) (addMod32 Q t3S) hbnd1).set
              (i2 + len + j2 + s) (subMod32 Q t3S) hbnd3) := by
  simp only [butterfly4, Bool.not_false, ite_true,
    vector_getD_eq_getElem roots _ ht1 0, vector_getD_eq_getElem roots _ ht2 0,
    vector_getD_eq_getElem roots _ ht3 0,
    dif_pos hbnd0, dif_pos hbnd1, dif_pos hbnd2, dif_pos hbnd3,
    Vector.get_eq_getElem]

lemma butterfly4_forward_getElem_pos0 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (ht1 : s + j2 < N) (ht2 : len + j2 < N) (ht3 : len + j2 + s < N)
    (hne10 : i2 + j2 + s ≠ i2 + j2)
    (hne20 : i2 + len + j2 ≠ i2 + j2)
    (hne30 : i2 + len + j2 + s ≠ i2 + j2) :
    let t1 := roots[s + j2]'ht1
    let t2 := roots[len + j2]'ht2
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let P := addMod32 (a[i2 + j2]'hbnd0) aB
    let R_v := addMod32 (a[i2 + len + j2]'hbnd2) aD
    let t2R := montMul t2 R_v
    (butterfly4 a false roots s len i2 j2)[i2 + j2]'hbnd0 = addMod32 P t2R := by
  rw [butterfly4_forward_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3 ht1 ht2 ht3]
  simp only []
  rw [Vector.getElem_set, if_neg hne30, Vector.getElem_set, if_neg hne10,
      Vector.getElem_set, if_neg hne20, Vector.getElem_set_self]

lemma butterfly4_forward_getElem_pos2 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (ht1 : s + j2 < N) (ht2 : len + j2 < N) (ht3 : len + j2 + s < N)
    (hne12 : i2 + j2 + s ≠ i2 + len + j2)
    (hne32 : i2 + len + j2 + s ≠ i2 + len + j2) :
    let t1 := roots[s + j2]'ht1
    let t2 := roots[len + j2]'ht2
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let P := addMod32 (a[i2 + j2]'hbnd0) aB
    let R_v := addMod32 (a[i2 + len + j2]'hbnd2) aD
    let t2R := montMul t2 R_v
    (butterfly4 a false roots s len i2 j2)[i2 + len + j2]'hbnd2 = subMod32 P t2R := by
  rw [butterfly4_forward_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3 ht1 ht2 ht3]
  simp only []
  rw [Vector.getElem_set, if_neg hne32, Vector.getElem_set, if_neg hne12,
      Vector.getElem_set_self]

lemma butterfly4_forward_getElem_pos1 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (ht1 : s + j2 < N) (ht2 : len + j2 < N) (ht3 : len + j2 + s < N)
    (hne31 : i2 + len + j2 + s ≠ i2 + j2 + s) :
    let t1 := roots[s + j2]'ht1
    let t3 := roots[len + j2 + s]'ht3
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let Q := subMod32 (a[i2 + j2]'hbnd0) aB
    let S_v := subMod32 (a[i2 + len + j2]'hbnd2) aD
    let t3S := montMul t3 S_v
    (butterfly4 a false roots s len i2 j2)[i2 + j2 + s]'hbnd1 = addMod32 Q t3S := by
  rw [butterfly4_forward_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3 ht1 ht2 ht3]
  simp only []
  rw [Vector.getElem_set, if_neg hne31, Vector.getElem_set_self]

lemma butterfly4_forward_getElem_pos3 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (ht1 : s + j2 < N) (ht2 : len + j2 < N) (ht3 : len + j2 + s < N) :
    let t1 := roots[s + j2]'ht1
    let t3 := roots[len + j2 + s]'ht3
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let Q := subMod32 (a[i2 + j2]'hbnd0) aB
    let S_v := subMod32 (a[i2 + len + j2]'hbnd2) aD
    let t3S := montMul t3 S_v
    (butterfly4 a false roots s len i2 j2)[i2 + len + j2 + s]'hbnd3 = subMod32 Q t3S := by
  rw [butterfly4_forward_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3 ht1 ht2 ht3]
  simp only []
  rw [Vector.getElem_set_self]

/-
  Level 3d – Preservation lemmas: positions untouched by butterfly4 / radix4Inner / radix4Middle.
-/

/-- `butterfly4` only modifies the four butterfly positions; all other positions are unchanged. -/
lemma butterfly4_getElem_ne {N : ℕ} (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (i : ℕ) (hi : i < N)
    (hne0 : i2 + j2 ≠ i) (hne1 : i2 + j2 + s ≠ i)
    (hne2 : i2 + len + j2 ≠ i) (hne3 : i2 + len + j2 + s ≠ i) :
    (butterfly4 a false roots s len i2 j2)[i]'hi = a[i]'hi := by
  simp only [butterfly4, Bool.not_false, ite_true,
    dif_pos hbnd0, dif_pos hbnd1, dif_pos hbnd2, dif_pos hbnd3]
  rw [Vector.getElem_set, if_neg hne3, Vector.getElem_set, if_neg hne1,
      Vector.getElem_set, if_neg hne2, Vector.getElem_set, if_neg hne0]

/-- `radix4Inner` leaves position `hi` unchanged if it is not any of the four butterfly
    positions for any `j2` in the processed range `[j2_start, j2_start + k)`. -/
lemma radix4Inner_getElem_ne {N : ℕ} (roots a : Vector UInt32 N)
    (s len i2 : ℕ) (k j2_start : ℕ) (hi : ℕ) (hlt : hi < N)
    (hbnd : ∀ j2, j2_start ≤ j2 → j2 < j2_start + k →
      i2 + j2 < N ∧ i2 + j2 + s < N ∧
      i2 + len + j2 < N ∧ i2 + len + j2 + s < N)
    (hne : ∀ j2, j2_start ≤ j2 → j2 < j2_start + k →
      i2 + j2 ≠ hi ∧ i2 + j2 + s ≠ hi ∧
      i2 + len + j2 ≠ hi ∧ i2 + len + j2 + s ≠ hi) :
    (radix4Inner false roots s len i2 k j2_start a)[hi]'hlt = a[hi]'hlt := by
  induction k generalizing j2_start a with
  | zero => rfl
  | succ k ih =>
    have hb := hbnd j2_start (le_refl _) (by omega)
    have hn := hne  j2_start (le_refl _) (by omega)
    calc (radix4Inner false roots s len i2 (k + 1) j2_start a)[hi]'hlt
        = (radix4Inner false roots s len i2 k (j2_start + 1)
            (butterfly4 a false roots s len i2 j2_start))[hi]'hlt := rfl
      _ = (butterfly4 a false roots s len i2 j2_start)[hi]'hlt :=
            ih (butterfly4 a false roots s len i2 j2_start) (j2_start + 1)
               (fun j2 hlo hhi => hbnd j2 (by omega) (by omega))
               (fun j2 hlo hhi => hne  j2 (by omega) (by omega))
      _ = a[hi]'hlt :=
            butterfly4_getElem_ne roots a s len i2 j2_start
               hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hi hlt hn.1 hn.2.1 hn.2.2.1 hn.2.2.2

/-- `radix4Middle` leaves position `hi` unchanged if it is not any butterfly position for
    any group `b` in `[b_start, b_start + k)` and any `j2 < s`. -/
lemma radix4Middle_getElem_ne {N : ℕ} (roots a : Vector UInt32 N)
    (s len : ℕ) (k b_start : ℕ) (hi : ℕ) (hlt : hi < N)
    (hbnd : ∀ b, b_start ≤ b → b < b_start + k → ∀ j2, j2 < s →
      let i2 := b * 2 * len
      i2 + j2 < N ∧ i2 + j2 + s < N ∧
      i2 + len + j2 < N ∧ i2 + len + j2 + s < N)
    (hne : ∀ b, b_start ≤ b → b < b_start + k → ∀ j2, j2 < s →
      let i2 := b * 2 * len
      i2 + j2 ≠ hi ∧ i2 + j2 + s ≠ hi ∧
      i2 + len + j2 ≠ hi ∧ i2 + len + j2 + s ≠ hi) :
    (radix4Middle false roots s len k b_start a)[hi]'hlt = a[hi]'hlt := by
  induction k generalizing b_start a with
  | zero => rfl
  | succ k ih =>
    calc (radix4Middle false roots s len (k + 1) b_start a)[hi]'hlt
        = (radix4Middle false roots s len k (b_start + 1)
            (radix4Inner false roots s len
              (b_start * 2 * len) s 0 a))[hi]'hlt := rfl
      _ = (radix4Inner false roots s len
              (b_start * 2 * len) s 0 a)[hi]'hlt :=
            ih (radix4Inner false roots s len
                  (b_start * 2 * len) s 0 a)
               (b_start + 1)
               (fun b hblo hbhi j2 hj2 => hbnd b (by omega) (by omega) j2 hj2)
               (fun b hblo hbhi j2 hj2 => hne  b (by omega) (by omega) j2 hj2)
      _ = a[hi]'hlt :=
            radix4Inner_getElem_ne roots a s len
               (b_start * 2 * len) s 0 hi hlt
               (fun j2 _ hj2 => hbnd b_start (le_refl _) (by omega) j2 (by omega))
               (fun j2 _ hj2 => hne  b_start (le_refl _) (by omega) j2 (by omega))

/- Level 3e – Composition lemma: splitting radix4Inner into two sequential calls. -/

lemma radix4Inner_comp {N : ℕ} (roots : Vector UInt32 N) (inverse : Bool)
    (s len i2 : ℕ) (k1 k2 j2_start : ℕ) (a : Vector UInt32 N) :
    radix4Inner inverse roots s len i2 (k1 + k2) j2_start a =
    radix4Inner inverse roots s len i2 k2 (j2_start + k1)
      (radix4Inner inverse roots s len i2 k1 j2_start a) := by
  induction k1 generalizing j2_start a with
  | zero => simp [radix4Inner]
  | succ k1 ih =>
    rw [show k1 + 1 + k2 = k1 + k2 + 1 by omega]
    simp only [radix4Inner]
    rw [ih (j2_start + 1) (butterfly4 a inverse roots s len i2 j2_start)]
    congr 1
    omega

/- Level 3f – butterfly4 ZMod-level correctness at the four output positions. -/

private lemma add_len_s_ne_zero_helper (s len : UInt64)
    (hlen : len.toNat = 2 * s.toNat) (hlen_lt : len.toNat < 2 ^ 64) (hs_pos : 0 < s.toNat) :
    len + s ≠ 0 := by
  have hnat : (len + s).toNat ≠ 0 := by
    rw [UInt64.toNat_add, hlen]
    rcases Nat.lt_or_ge (2 * s.toNat + s.toNat) (2 ^ 64) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]; omega
  exact fun h => hnat (by simp [h])

private lemma add_shifted_ne_helper (s len i2 j2 : UInt64)
    (hlen : len.toNat = 2 * s.toNat) (hlen_lt : len.toNat < 2 ^ 64)
    (hs_pos : 0 < s.toNat) (hi2j2_lt : (i2 + j2).toNat < 2 ^ 64) :
    i2 + len + j2 + s ≠ i2 + j2 := by
  have hnat : (i2 + len + j2 + s).toNat ≠ (i2 + j2).toNat := by
    have hlens_pos : (len + s).toNat ≠ 0 := by
      rw [UInt64.toNat_add, hlen]
      rcases Nat.lt_or_ge (2 * s.toNat + s.toNat) (2 ^ 64) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt]; omega
      · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]; omega
    have hls_lt : (len + s).toNat < 2 ^ 64 := (len + s).toNat_lt
    have h1 : (i2 + len + j2 + s).toNat = ((i2 + j2).toNat + (len + s).toNat) % 2 ^ 64 := by
      have : i2 + len + j2 + s = (i2 + j2) + (len + s) := by abel
      rw [this]; exact UInt64.toNat_add (i2 + j2) (len + s)
    rw [h1]
    rcases Nat.lt_or_ge ((i2 + j2).toNat + (len + s).toNat) (2^64) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]; omega
  exact fun h => hnat (congr_arg UInt64.toNat h)

private lemma butterfly4_forward_idx_bounds {N : ℕ} (s len j2 : UInt64)
    (hlen : len.toNat = 2 * s.toNat) (hlen_dvd : 2 * len.toNat ∣ N)
    (hj2 : j2.toNat < s.toNat) (hN_le : N ≤ 2 ^ 64) (hN_pos : 0 < N) :
    (s + j2).toNat < N ∧ (len + j2).toNat < N ∧ (len + j2 + s).toNat < N := by
  have h_s_j2 : (s + j2).toNat < N := by
    simp only [UInt64.toNat_add] at *
    norm_num [hlen] at hlen_dvd hN_le
    exact lt_of_le_of_lt (Nat.mod_le _ _)
      (by linarith [Nat.le_of_dvd hN_pos hlen_dvd])
  refine ⟨h_s_j2, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hlen_dvd
    have hk_pos : 0 < k := Nat.pos_of_ne_zero (by intro h; simp [h] at hk; omega)
    rw [UInt64.toNat_add] at *
    rw [Nat.mod_eq_of_lt] <;> nlinarith
  · obtain ⟨k, hk⟩ := hlen_dvd
    rcases k with (_ | _ | k) <;>
      simp_all +decide only [UInt64.toNat_add, Nat.reducePow,
                             Nat.mod_add_mod, Nat.mul_zero, lt_irrefl]
    · omega
    · rw [Nat.mod_eq_of_lt] <;> nlinarith only [hj2, hN_le]

private lemma butterfly4_forward_idx_bounds_nat {N : ℕ} (s len j2 : ℕ)
    (hlen : len = 2 * s) (hlen_dvd : 2 * len ∣ N) (hj2 : j2 < s) (hN_pos : 0 < N) :
    s + j2 < N ∧ len + j2 < N ∧ len + j2 + s < N := by
  have h2len_le : 2 * len ≤ N := Nat.le_of_dvd hN_pos hlen_dvd
  omega

-- Root ZMod values for the three forward butterfly twiddle positions,
-- proved once for all pos lemmas.
private lemma butterfly4_forward_root_values {N : ℕ}
    (roots : Vector UInt32 N) (hroots : ntt_roots_correct N roots)
    (s len j2 : ℕ) (hlen : len = 2 * s) (hlen_dvd : 2 * len ∣ N) (hj2 : j2 < s)
    (ht1 : s + j2 < N) (ht2 : len + j2 < N) (ht3 : len + j2 + s < N) :
    ((roots[s + j2]'ht1).toNat : ZMod mod32.toNat) =
        (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2)
          * (montR1.toNat : ZMod mod32.toNat) ∧
    ((roots[len + j2]'ht2).toNat : ZMod mod32.toNat) =
        (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * j2)
          * (montR1.toNat : ZMod mod32.toNat) ∧
    ((roots[len + j2 + s]'ht3).toNat : ZMod mod32.toNat) =
        (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * (s + j2))
          * (montR1.toNat : ZMod mod32.toNat) := by
  refine ⟨?_, ?_, ?_⟩
  · apply ntt_roots_correct_at
    · assumption
    · omega
    · exact dvd_of_mul_left_dvd hlen_dvd
    · omega
    · omega
  · convert ntt_roots_correct_at roots hroots (2 * len) j2 (len + j2) _ _ _ _ using 1
    any_goals omega
    simp +decide
  · convert ntt_roots_correct_at roots hroots (2 * len) (s + j2) (len + j2 + s) _ _ _ _ using 1
    any_goals omega
    simp +decide [add_comm, add_left_comm]

-- Element and root bounds for forward butterfly4 inputs, proved once for all pos lemmas.
private lemma butterfly4_forward_bounds {N : ℕ}
    (a : Vector UInt32 N) (ha : a.all (· < mod32))
    (roots : Vector UInt32 N) (hroots_bnd : roots.all (· < mod32))
    (i2 j2 s len : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (ht1 : s + j2 < N) (ht2 : len + j2 < N) (ht3 : len + j2 + s < N) :
    (a[i2 + j2]'hbnd0).toNat < mod32.toNat ∧
    (a[i2 + j2 + s]'hbnd1).toNat < mod32.toNat ∧
    (a[i2 + len + j2]'hbnd2).toNat < mod32.toNat ∧
    (a[i2 + len + j2 + s]'hbnd3).toNat < mod32.toNat ∧
    (roots[s + j2]'ht1).toNat < mod32.toNat ∧
    (roots[len + j2]'ht2).toNat < mod32.toNat ∧
    (roots[len + j2 + s]'ht3).toNat < mod32.toNat := by
  simp only [Vector.all_eq_true, decide_eq_true_eq] at ha hroots_bnd
  exact ⟨UInt32.lt_iff_toNat_lt.mp (ha _ hbnd0),
         UInt32.lt_iff_toNat_lt.mp (ha _ hbnd1),
         UInt32.lt_iff_toNat_lt.mp (ha _ hbnd2),
         UInt32.lt_iff_toNat_lt.mp (ha _ hbnd3),
         UInt32.lt_iff_toNat_lt.mp (hroots_bnd _ ht1),
         UInt32.lt_iff_toNat_lt.mp (hroots_bnd _ ht2),
         UInt32.lt_iff_toNat_lt.mp (hroots_bnd _ ht3)⟩

lemma butterfly4_forward_ZMod_pos0 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hN_le : N ≤ 2 ^ 64) :
    ((butterfly4 a false roots s len i2 j2)[i2 + j2]'hbnd0).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
        (a[i2 + j2 + s]'hbnd1).toNat +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * j2) *
        ((a[i2 + len + j2]'hbnd2).toNat +
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have h_idx_bounds := butterfly4_forward_idx_bounds_nat s len j2 hlen hlen_dvd hj2 (by omega)
  have hlen_pos : len > 0 := by omega
  have hne10 : i2 + j2 + s ≠ i2 + j2 := by omega
  have hne20 : i2 + len + j2 ≠ i2 + j2 := by omega
  have hne30 : i2 + len + j2 + s ≠ i2 + j2 := by omega
  rw [ butterfly4_forward_getElem_pos0 ];
  any_goals (first | assumption | exact h_idx_bounds.1 |
    exact h_idx_bounds.2.1 | exact h_idx_bounds.2.2);
  rw [ addmod32_ZMod, mont_mul_ZMod ];
  · rw [ addmod32_ZMod, addmod32_ZMod ];
    · rw [ mont_mul_ZMod, mont_mul_ZMod ];
      · have h_root_values :
            ((roots[s + j2]'h_idx_bounds.left).toNat : ZMod mod32.toNat) =
              (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
              (montR1.toNat : ZMod mod32.toNat) ∧
            ((roots[len + j2]'h_idx_bounds.right.left).toNat : ZMod mod32.toNat) =
              (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * j2) *
              (montR1.toNat : ZMod mod32.toNat) := by
          apply And.intro;
          · apply ntt_roots_correct_at;
            · assumption;
            · omega;
            · exact dvd_of_mul_left_dvd hlen_dvd;
            · omega;
            · omega;
          · convert ntt_roots_correct_at roots hroots ( 2 * len ) j2 ( len + j2 ) _ _ _ _ using 1;
            any_goals omega;
            simp +decide;
        rw [h_root_values.1, h_root_values.2, MONT_R1_ZMod]
        simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
          mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
        ring
      · have h_all : ∀ x ∈ a, x.toNat < mod32.toNat := by
          rw [ Vector.all_eq_true ] at ha;
          intro x hx; obtain ⟨ i, hi ⟩ := Vector.mem_iff_getElem.mp hx; specialize ha i; aesop;
        exact h_all _ ( by simp );
      · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
        convert hroots_bnd _ _;
      · rw [ Vector.all_eq_true ] at ha;
        specialize ha ( i2 + j2 + s ) hbnd1 ; aesop;
      · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
        convert hroots_bnd _ _;
    · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert ha _ _;
    · apply mont_mul_lt_of_right;
      simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert hroots_bnd _ _;
    · have := ha; simp_all only [Vector.all_eq_true, decide_eq_true_eq] ;
      convert this _ _;
    · apply mont_mul_lt_of_left;
      rw [ Vector.all_eq_true ] at ha;
      specialize ha ( i2 + j2 + s ) hbnd1 ; aesop;
  · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
    convert hroots_bnd _ _;
  · apply addmod32_lt;
    · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert ha _ _;
    · apply mont_mul_lt_of_right;
      simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert hroots_bnd _ _;
  · apply addmod32_lt;
    · have := ha; simp_all only [Vector.all_eq_true, decide_eq_true_eq] ;
      convert this _ _;
    · apply mont_mul_lt_of_left;
      rw [ Vector.all_eq_true ] at ha;
      specialize ha ( i2 + j2 + s ) hbnd1 ; aesop;
  · apply mont_mul_lt_of_left;
    simp_all only [Vector.all_eq_true, decide_eq_true_eq];
    convert hroots_bnd _ _

-- The ZMod correctness proof for butterfly4 at position 2 uses many rewriting steps.
lemma butterfly4_forward_ZMod_pos2 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hN_le : N ≤ 2 ^ 64) :
    ((butterfly4 a false roots s len i2 j2)[i2 + len + j2]'hbnd2).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
        (a[i2 + j2 + s]'hbnd1).toNat -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * j2) *
        ((a[i2 + len + j2]'hbnd2).toNat +
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have h_idx_bounds := butterfly4_forward_idx_bounds_nat s len j2 hlen hlen_dvd hj2 (by omega)
  have hlen_pos : len > 0 := by omega
  have hne12 : i2 + j2 + s ≠ i2 + len + j2 := by omega
  have hne32 : i2 + len + j2 + s ≠ i2 + len + j2 := by omega
  rw [ butterfly4_forward_getElem_pos2 roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3
      h_idx_bounds.left h_idx_bounds.right.left h_idx_bounds.right.right hne12 hne32 ];
  rw [ submod32_ZMod, mont_mul_ZMod ];
  · rw [ addmod32_ZMod, addmod32_ZMod ];
    · rw [ mont_mul_ZMod, mont_mul_ZMod ];
      · have h_root_values :
              ((roots[s + j2]'h_idx_bounds.left).toNat : ZMod mod32.toNat) =
                (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
                (montR1.toNat : ZMod mod32.toNat) ∧
              ((roots[len + j2]'h_idx_bounds.right.left).toNat : ZMod mod32.toNat) =
                (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * j2) *
                (montR1.toNat : ZMod mod32.toNat) := by
            apply And.intro;
            · apply ntt_roots_correct_at;
              · assumption;
              · omega;
              · exact dvd_of_mul_left_dvd hlen_dvd;
              · omega;
              · omega;
            · convert ntt_roots_correct_at roots hroots ( 2 * len ) j2 ( len + j2 ) _ _ _ _ using 1;
              any_goals omega;
              simp +decide;
        rw [h_root_values.1, h_root_values.2, MONT_R1_ZMod]
        simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
          mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
        ring
      · have h_all : ∀ x ∈ a, x.toNat < mod32.toNat := by
          rw [ Vector.all_eq_true ] at ha;
          intro x hx; obtain ⟨ i, hi ⟩ := Vector.mem_iff_getElem.mp hx; specialize ha i; aesop;
        exact h_all _ ( by simp );
      · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
        convert hroots_bnd _ _;
      · rw [ Vector.all_eq_true ] at ha;
        specialize ha ( i2 + j2 + s ) hbnd1 ; aesop;
      · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
        convert hroots_bnd _ _;
    · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert ha _ _;
    · apply mont_mul_lt_of_right;
      simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert hroots_bnd _ _;
    · have := ha; simp_all only [Vector.all_eq_true, decide_eq_true_eq] ;
      convert this _ _;
    · apply mont_mul_lt_of_left;
      rw [ Vector.all_eq_true ] at ha;
      specialize ha ( i2 + j2 + s ) hbnd1 ; aesop;
  · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
    convert hroots_bnd _ _;
  · apply addmod32_lt;
    · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert ha _ _;
    · apply mont_mul_lt_of_right;
      simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert hroots_bnd _ _;
  · apply addmod32_lt;
    · have := ha; simp_all only [Vector.all_eq_true, decide_eq_true_eq] ;
      convert this _ _;
    · apply mont_mul_lt_of_left;
      rw [ Vector.all_eq_true ] at ha;
      specialize ha ( i2 + j2 + s ) hbnd1 ; aesop;
  · apply mont_mul_lt_of_left;
    simp_all only [Vector.all_eq_true, decide_eq_true_eq];
    convert hroots_bnd _ _

-- The ZMod correctness proof for butterfly4 at position 1 uses many rewriting steps.
lemma butterfly4_forward_ZMod_pos1 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hN_le : N ≤ 2 ^ 64) :
    ((butterfly4 a false roots s len i2 j2)[i2 + j2 + s]'hbnd1).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
        (a[i2 + j2 + s]'hbnd1).toNat +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (s + j2)) *
        ((a[i2 + len + j2]'hbnd2).toNat -
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have h_idx_bounds := butterfly4_forward_idx_bounds_nat s len j2 hlen hlen_dvd hj2 (by omega)
  have hlen_pos : len > 0 := by omega
  have hne31 : i2 + len + j2 + s ≠ i2 + j2 + s := by omega
  rw [ butterfly4_forward_getElem_pos1 roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3
      h_idx_bounds.left h_idx_bounds.right.left h_idx_bounds.right.right hne31 ];
  rw [ addmod32_ZMod, mont_mul_ZMod ];
  · rw [ submod32_ZMod, submod32_ZMod ];
    · rw [ mont_mul_ZMod, mont_mul_ZMod ];
      · have h_root_values :
              ((roots[s + j2]'h_idx_bounds.left).toNat : ZMod mod32.toNat) =
                (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
                (montR1.toNat : ZMod mod32.toNat) ∧
              ((roots[len + j2 + s]'h_idx_bounds.right.right).toNat : ZMod mod32.toNat) =
                (primRoot.toNat : ZMod mod32.toNat) ^
                ((mod64.toNat - 1) / (2 * len) * (s + j2)) *
                (montR1.toNat : ZMod mod32.toNat) := by
          apply And.intro;
          · apply ntt_roots_correct_at;
            · assumption;
            · omega;
            · exact dvd_of_mul_left_dvd hlen_dvd;
            · omega;
            · omega;
          · convert ntt_roots_correct_at roots hroots ( 2 * len ) ( s + j2 )
                  ( len + j2 + s ) _ _ _ _ using 1;
            any_goals omega;
            simp +decide [ add_comm, add_left_comm ];
        rw [h_root_values.1, h_root_values.2, MONT_R1_ZMod]
        simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
          mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
        ring
      · have h_all : ∀ x ∈ a, x.toNat < mod32.toNat := by
          rw [ Vector.all_eq_true ] at ha;
          intro x hx; obtain ⟨ i, hi ⟩ := Vector.mem_iff_getElem.mp hx; specialize ha i; aesop;
        exact h_all _ ( by simp );
      · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
        convert hroots_bnd _ _;
      · rw [ Vector.all_eq_true ] at ha;
        specialize ha ( i2 + j2 + s ) hbnd1 ; aesop;
      · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
        convert hroots_bnd _ _;
    · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert ha _ _;
    · apply mont_mul_lt_of_right;
      simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert hroots_bnd _ _;
    · have := ha; simp_all only [Vector.all_eq_true, decide_eq_true_eq] ;
      convert this _ _;
    · apply mont_mul_lt_of_left;
      rw [ Vector.all_eq_true ] at ha;
      specialize ha ( i2 + j2 + s ) hbnd1 ; aesop;
  · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
    convert hroots_bnd _ _;
  · apply submod32_lt;
    · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert ha _ _;
    · apply mont_mul_lt_of_right;
      simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert hroots_bnd _ _;
  · apply submod32_lt;
    · have := ha; simp_all only [Vector.all_eq_true, decide_eq_true_eq] ;
      convert this _ _;
    · apply mont_mul_lt_of_left;
      rw [ Vector.all_eq_true ] at ha;
      specialize ha ( i2 + j2 + s ) hbnd1 ; aesop;
  · apply mont_mul_lt_of_left;
    simp_all only [Vector.all_eq_true, decide_eq_true_eq];
    convert hroots_bnd _ _

-- The ZMod correctness proof for butterfly4 at position 3 uses many rewriting steps.
lemma butterfly4_forward_ZMod_pos3 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hN_le : N ≤ 2 ^ 64) :
    ((butterfly4 a false roots s len i2 j2)[i2 + len + j2 + s]'hbnd3).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
        (a[i2 + j2 + s]'hbnd1).toNat -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (s + j2)) *
        ((a[i2 + len + j2]'hbnd2).toNat -
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have h_idx_bounds := butterfly4_forward_idx_bounds_nat s len j2 hlen hlen_dvd hj2 (by omega)
  rw [ butterfly4_forward_getElem_pos3 ];
  any_goals tauto;
  rw [ submod32_ZMod, mont_mul_ZMod ];
  · rw [ submod32_ZMod, submod32_ZMod ];
    · rw [ mont_mul_ZMod, mont_mul_ZMod ];
      · have h_root_values :
              ((roots[s + j2]'h_idx_bounds.left).toNat : ZMod mod32.toNat) =
                (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2) *
                (montR1.toNat : ZMod mod32.toNat) ∧
              ((roots[len + j2 + s]'h_idx_bounds.right.right).toNat : ZMod mod32.toNat) =
                (primRoot.toNat : ZMod mod32.toNat) ^
                ((mod64.toNat - 1) / (2 * len) * (s + j2)) *
                (montR1.toNat : ZMod mod32.toNat) := by
          apply And.intro;
          · apply ntt_roots_correct_at;
            · assumption;
            · omega;
            · exact dvd_of_mul_left_dvd hlen_dvd;
            · omega;
            · omega;
          · convert ntt_roots_correct_at roots hroots ( 2 * len ) ( s + j2 )
                  ( len + j2 + s ) _ _ _ _ using 1;
            any_goals omega;
            simp +decide [ add_comm, add_left_comm ];
        rw [h_root_values.1, h_root_values.2, MONT_R1_ZMod]
        simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
          mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
        ring
      · have h_all : ∀ x ∈ a, x.toNat < mod32.toNat := by
          rw [ Vector.all_eq_true ] at ha;
          intro x hx; obtain ⟨ i, hi ⟩ := Vector.mem_iff_getElem.mp hx; specialize ha i; aesop;
        exact h_all _ ( by simp );
      · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
        convert hroots_bnd _ _;
      · rw [ Vector.all_eq_true ] at ha;
        specialize ha ( i2 + j2 + s ) hbnd1 ; aesop;
      · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
        convert hroots_bnd _ _;
    · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert ha _ _;
    · apply mont_mul_lt_of_right;
      simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert hroots_bnd _ _;
    · have := ha; simp_all only [Vector.all_eq_true, decide_eq_true_eq] ;
      convert this _ _;
    · apply mont_mul_lt_of_left;
      rw [ Vector.all_eq_true ] at ha;
      specialize ha ( i2 + j2 + s ) hbnd1 ; aesop;
  · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
    convert hroots_bnd _ _;
  · apply submod32_lt;
    · simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert ha _ _;
    · apply mont_mul_lt_of_right;
      simp_all only [Vector.all_eq_true, decide_eq_true_eq];
      convert hroots_bnd _ _;
  · apply submod32_lt;
    · have := ha; simp_all only [Vector.all_eq_true, decide_eq_true_eq] ;
      convert this _ _;
    · apply mont_mul_lt_of_left;
      rw [ Vector.all_eq_true ] at ha;
      specialize ha ( i2 + j2 + s ) hbnd1 ; aesop;
  · apply mont_mul_lt_of_left;
    simp_all only [Vector.all_eq_true, decide_eq_true_eq];
    convert hroots_bnd _ _

lemma butterfly4_forward_ZMod_combined {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hN_le : N ≤ 2 ^ 64) :
    let τ₁ : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * j2)
    let τ₂ : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * j2)
    let τ₃ : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (s + j2))
    let r  := butterfly4 a false roots s len i2 j2
    let A₀ := ((a[i2 + j2]'hbnd0).toNat       : ZMod mod32.toNat)
    let A₁ := ((a[i2 + j2 + s]'hbnd1).toNat   : ZMod mod32.toNat)
    let A₂ := ((a[i2 + len + j2]'hbnd2).toNat : ZMod mod32.toNat)
    let A₃ := ((a[i2 + len + j2 + s]'hbnd3).toNat : ZMod mod32.toNat)
    ((r[i2 + j2]'hbnd0).toNat           : ZMod mod32.toNat) =
        A₀ + τ₁ * A₁ + τ₂ * (A₂ + τ₁ * A₃) ∧
    ((r[i2 + len + j2]'hbnd2).toNat     : ZMod mod32.toNat) =
        A₀ + τ₁ * A₁ - τ₂ * (A₂ + τ₁ * A₃) ∧
    ((r[i2 + j2 + s]'hbnd1).toNat       : ZMod mod32.toNat) =
        A₀ - τ₁ * A₁ + τ₃ * (A₂ - τ₁ * A₃) ∧
    ((r[i2 + len + j2 + s]'hbnd3).toNat : ZMod mod32.toNat) =
        A₀ - τ₁ * A₁ - τ₃ * (A₂ - τ₁ * A₃) := by
  simp only []
  exact ⟨butterfly4_forward_ZMod_pos0 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hj2 hbnd0 hbnd1 hbnd2 hbnd3 hN_le,
  butterfly4_forward_ZMod_pos2 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hj2 hbnd0 hbnd1 hbnd2 hbnd3 hN_le,
  butterfly4_forward_ZMod_pos1 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hj2 hbnd0 hbnd1 hbnd2 hbnd3 hN_le,
  butterfly4_forward_ZMod_pos3 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hj2 hbnd0 hbnd1 hbnd2 hbnd3 hN_le⟩

/-
  Level 3g – butterfly4 inverse: structural and ZMod-level correctness.

  The inverse butterfly uses negated twiddles: instead of `roots[s+j2]` for t1 it uses
  `mod32 - roots[2*s - j2]` (when `j2 > 0`) which equals `-roots[2*s - j2]` in ZMod
  (and similarly for t2, t3). Since `mod64 = 3*2^30 + 1`, we have
  `primRoot^{(mod64-1)/2} = -1` in ZMod mod64, so the negated twiddle equals
  `ω^{(mod64-1)/len * (len - j2)} * R` where `ω = primRoot`.
-/

/-- Negation of a `UInt32 < mod32` in `ZMod mod32.toNat`:
    `(mod32 - r).toNat ≡ -r` (mod `mod32`). -/
lemma neg_root_zmod (r : UInt32) (hr : r.toNat < mod32.toNat) :
    ((mod32 - r).toNat : ZMod mod32.toNat) = -(r.toNat : ZMod mod32.toNat) := by
  have h1 : mod32.toNat = 3221225473 := by decide
  by_cases hpos : 0 < r.toNat
  · have heq : (mod32 - r).toNat = mod32.toNat - r.toNat := by
      rw [UInt32.toNat_sub]; omega
    rw [heq]
    have hle : r.toNat ≤ mod32.toNat := le_of_lt hr
    rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub]
  · push Not at hpos
    have hr_zero : r.toNat = 0 := Nat.le_zero.mp hpos
    have heq : (mod32 - r).toNat = mod32.toNat := by
      have hr_eq : r = 0 := UInt32.toNat_inj.mp (by rw [hr_zero]; rfl)
      rw [hr_eq, sub_zero]
    rw [heq, hr_zero]
    simp

/-- Key Nat arithmetic identity: when `len = 2 * s` and `2 * len ∣ m`,
    `m / len * (s - j2) + m / 2 = m / len * (len - j2)` (for `j2 < s`).
    This is what makes the inverse twiddle computation work for `t1`, `t2`. -/
lemma twiddle_neg_exp_identity (m len s j2 : ℕ)
    (hlen : len = 2 * s) (hdvd : 2 * len ∣ m) (hj2 : j2 < s) :
    m / len * (s - j2) + m / 2 = m / len * (len - j2) := by
  obtain ⟨k, hk⟩ := hdvd
  subst hk
  rw [hlen]
  have h1 : 2 * (2 * s) * k / (2 * s) = 2 * k := by
    rw [show 2 * (2 * s) * k = (2 * s) * (2 * k) by ring]
    exact Nat.mul_div_cancel_left _ (by omega : 0 < 2 * s)
  have h2 : 2 * (2 * s) * k / 2 = (2 * s) * k := by
    rw [show 2 * (2 * s) * k = 2 * ((2 * s) * k) by ring]
    exact Nat.mul_div_cancel_left _ (by omega : 0 < 2)
  rw [h1, h2]
  have hsj2 : j2 ≤ s := le_of_lt hj2
  have h2sj2 : j2 ≤ 2 * s := by omega
  rw [Nat.mul_sub, Nat.mul_sub]
  have hkj2_le1 : 2 * k * j2 ≤ 2 * k * s := Nat.mul_le_mul_left _ hsj2
  have hkj2_le2 : 2 * k * j2 ≤ 2 * k * (2 * s) := Nat.mul_le_mul_left _ h2sj2
  have hkkk : 2 * k * (2 * s) = 2 * k * s + 2 * s * k := by ring
  omega

/-- Variant Nat arithmetic identity for the `t2` twiddle (with `len' = 2*len, s' = len`):
    when `2 * len ∣ m` and `2 ∣ m`,
    `m / (2 * len) * (len - j2) + m / 2 = m / (2 * len) * (2 * len - j2)`
    for `j2 ≤ len`. -/
lemma twiddle_neg_exp_identity_t2 (m len j2 : ℕ)
    (hdvd : 2 * len ∣ m) (h2_dvd : 2 ∣ m) (hj2 : j2 ≤ len) :
    m / (2 * len) * (len - j2) + m / 2 = m / (2 * len) * (2 * len - j2) := by
  obtain ⟨k, hk⟩ := hdvd
  subst hk
  by_cases hlen_pos : len > 0
  · have h1 : 2 * len * k / (2 * len) = k :=
      Nat.mul_div_cancel_left _ (by omega : 0 < 2 * len)
    have h2 : 2 * len * k / 2 = len * k := by
      rw [show 2 * len * k = 2 * (len * k) by ring]
      exact Nat.mul_div_cancel_left _ (by omega : 0 < 2)
    rw [h1, h2, Nat.mul_sub, Nat.mul_sub]
    have h2lk : k * j2 ≤ k * (2 * len) := Nat.mul_le_mul_left _ (by omega)
    have hlk : k * j2 ≤ k * len := Nat.mul_le_mul_left _ hj2
    have h_2l : k * (2 * len) = k * len + len * k := by ring
    omega
  · push Not at hlen_pos
    interval_cases len
    have : j2 = 0 := by omega
    subst this
    simp

/-- Key Nat arithmetic identity for the `t3` twiddle: when `len = 2 * s` and `2 * len ∣ m`,
    `m / (2 * len) * (s - j2) + m / 2 = m / (2 * len) * (2 * len - s - j2)`. -/
lemma twiddle_neg_exp_identity_t3 (m len s j2 : ℕ)
    (hlen : len = 2 * s) (hdvd : 2 * len ∣ m) (hj2 : j2 < s) :
    m / (2 * len) * (s - j2) + m / 2 = m / (2 * len) * (2 * len - s - j2) := by
  obtain ⟨k, hk⟩ := hdvd
  subst hk
  rw [hlen]
  have h1 : 2 * (2 * s) * k / (2 * (2 * s)) = k :=
    Nat.mul_div_cancel_left _ (by omega : 0 < 2 * (2 * s))
  have h2 : 2 * (2 * s) * k / 2 = (2 * s) * k := by
    rw [show 2 * (2 * s) * k = 2 * ((2 * s) * k) by ring]
    exact Nat.mul_div_cancel_left _ (by omega : 0 < 2)
  rw [h1, h2]
  have hsj2 : j2 ≤ s := le_of_lt hj2
  have h3 : 2 * (2 * s) - s - j2 = 3 * s - j2 := by omega
  rw [h3, Nat.mul_sub k s j2, Nat.mul_sub k (3 * s) j2]
  have hkj2 : k * j2 ≤ k * s := Nat.mul_le_mul_left _ hsj2
  have hk3s : k * j2 ≤ k * (3 * s) := Nat.mul_le_mul_left _ (by omega)
  have h_k3s : k * (3 * s) = k * s + 2 * s * k := by ring
  omega

-- Shared expansion: unfolds butterfly4 (inverse) into the explicit Vector.set chain once,
-- absorbing the expensive simp only [butterfly4, ...] cost for all four getElem_posX lemmas.
private lemma butterfly4_inverse_expand {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N) :
    butterfly4 a true roots s len i2 j2 =
      let t1 : UInt32 :=
        if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0
      let t2 : UInt32 :=
        if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0 else roots.getD len 0
      let t3 : UInt32 := mod32 - roots.getD (2 * len - j2 - s) 0
      let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
      let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
      let P  := addMod32 (a[i2 + j2]'hbnd0) aB
      let Rv := addMod32 (a[i2 + len + j2]'hbnd2) aD
      let Q  := subMod32 (a[i2 + j2]'hbnd0) aB
      let Sv := subMod32 (a[i2 + len + j2]'hbnd2) aD
      let t2R := montMul t2 Rv
      let t3S := montMul t3 Sv
      ((((a.set (i2 + j2) (addMod32 P t2R) hbnd0).set
               (i2 + len + j2) (subMod32 P t2R) hbnd2).set
               (i2 + j2 + s) (addMod32 Q t3S) hbnd1).set
               (i2 + len + j2 + s) (subMod32 Q t3S) hbnd3) := by
  simp only [butterfly4, Bool.not_true, Bool.false_eq_true, ite_false,
    dif_pos hbnd0, dif_pos hbnd1, dif_pos hbnd2, dif_pos hbnd3,
    Vector.get_eq_getElem]

-- Structural: what `butterfly4` returns at position `(i2 + j2)` for `inverse=true`.
lemma butterfly4_inverse_getElem_pos0 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hne10 : i2 + j2 + s ≠ i2 + j2)
    (hne20 : i2 + len + j2 ≠ i2 + j2)
    (hne30 : i2 + len + j2 + s ≠ i2 + j2) :
    let t1 : UInt32 :=
      if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0
    let t2 : UInt32 :=
      if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0 else roots.getD len 0
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let P := addMod32 (a[i2 + j2]'hbnd0) aB
    let R_v := addMod32 (a[i2 + len + j2]'hbnd2) aD
    let t2R := montMul t2 R_v
    (butterfly4 a true roots s len i2 j2)[i2 + j2]'hbnd0 = addMod32 P t2R := by
  rw [butterfly4_inverse_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3]
  simp only []
  rw [Vector.getElem_set, if_neg hne30, Vector.getElem_set, if_neg hne10,
      Vector.getElem_set, if_neg hne20, Vector.getElem_set_self]

-- Structural: what `butterfly4` returns at position `(i2 + len + j2)` for `inverse=true`.
lemma butterfly4_inverse_getElem_pos2 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hne12 : i2 + j2 + s ≠ i2 + len + j2)
    (hne32 : i2 + len + j2 + s ≠ i2 + len + j2) :
    let t1 : UInt32 :=
      if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0
    let t2 : UInt32 :=
      if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0 else roots.getD len 0
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let P := addMod32 (a[i2 + j2]'hbnd0) aB
    let R_v := addMod32 (a[i2 + len + j2]'hbnd2) aD
    let t2R := montMul t2 R_v
    (butterfly4 a true roots s len i2 j2)[i2 + len + j2]'hbnd2 = subMod32 P t2R := by
  rw [butterfly4_inverse_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3]
  simp only []
  rw [Vector.getElem_set, if_neg hne32, Vector.getElem_set, if_neg hne12,
      Vector.getElem_set_self]

-- Structural: what `butterfly4` returns at position `(i2 + j2 + s)` for `inverse=true`.
lemma butterfly4_inverse_getElem_pos1 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hne31 : i2 + len + j2 + s ≠ i2 + j2 + s) :
    let t1 : UInt32 :=
      if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0
    let t3 : UInt32 := mod32 - roots.getD (2 * len - j2 - s) 0
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let Q := subMod32 (a[i2 + j2]'hbnd0) aB
    let S_v := subMod32 (a[i2 + len + j2]'hbnd2) aD
    let t3S := montMul t3 S_v
    (butterfly4 a true roots s len i2 j2)[i2 + j2 + s]'hbnd1 = addMod32 Q t3S := by
  rw [butterfly4_inverse_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3]
  simp only []
  rw [Vector.getElem_set, if_neg hne31, Vector.getElem_set_self]

-- Structural: what `butterfly4` returns at position `(i2 + len + j2 + s)` for `inverse=true`.
lemma butterfly4_inverse_getElem_pos3 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N) :
    let t1 : UInt32 :=
      if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0
    let t3 : UInt32 := mod32 - roots.getD (2 * len - j2 - s) 0
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let Q := subMod32 (a[i2 + j2]'hbnd0) aB
    let S_v := subMod32 (a[i2 + len + j2]'hbnd2) aD
    let t3S := montMul t3 S_v
    (butterfly4 a true roots s len i2 j2)[i2 + len + j2 + s]'hbnd3 = subMod32 Q t3S := by
  rw [butterfly4_inverse_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3]
  simp only []
  rw [Vector.getElem_set_self]

/-- Helper: a root value at a valid NTT index is `< mod32`, and its negation `mod32 - r`
    is also `< mod32` (because ω^e * R is nonzero in `ZMod mod32.toNat`). -/
lemma inverse_twiddle_bound {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots) (hroots_bnd : roots.all (· < mod32))
    (len' j' : ℕ) (h2 : 2 ≤ len') (hdvd : len' ∣ N) (hj' : j' < len' / 2)
    (idx : ℕ) (hidx : idx < N) (heq : idx = len' / 2 + j') :
    (mod32 - roots[idx]'hidx).toNat < mod32.toNat := by
  have hroot_lt : (roots[idx]'hidx).toNat < mod32.toNat := by
    rw [Vector.all_eq_true] at hroots_bnd
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using hroots_bnd _ hidx)
  have hroot_val := ntt_roots_correct_at roots hroots len' j' idx h2 hdvd hj' hidx heq
  have hne : ((roots[idx]'hidx).toNat : ZMod mod32.toNat) ≠ 0 := by
    rw [hroot_val]
    have hp : (primRoot.toNat : ZMod mod32.toNat) ≠ 0 := prim_root_ne_zero_ZMod
    have hR : (montR1.toNat : ZMod mod32.toNat) ≠ 0 := mont_r1_ne_zero_ZMod
    exact mul_ne_zero (pow_ne_zero _ hp) hR
  have hpos : (roots[idx]'hidx).toNat > 0 := by
    by_contra h
    push Not at h
    have : (roots[idx]'hidx).toNat = 0 := Nat.le_zero.mp h
    rw [this] at hne; simp at hne
  have h1 : mod32.toNat = 3221225473 := by decide
  rw [UInt32.toNat_sub]
  omega

-- Helper: ZMod value of inverse `t1` twiddle.
lemma inverse_t1_zmod {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots) (hroots_bnd : roots.all (· < mod32))
    (s len j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (h_idx_pos : 2 * s - j2 < N)
    (h_idx_pos_eq : 2 * s - j2 = s + (s - j2))
    (h_idx_zero : s < N) :
    ((if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0
      else roots.getD s 0).toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2))
        * (montR1.toNat : ZMod mod32.toNat) := by
  by_cases hj2_pos : j2 > 0
  · rw [if_pos hj2_pos]
    rw [vector_getD_eq_getElem roots _ h_idx_pos 0]
    have hroots_bnd_at : (roots[2 * s - j2]'h_idx_pos).toNat < mod32.toNat := by
      rw [Vector.all_eq_true] at hroots_bnd
      exact UInt32.lt_iff_toNat_lt.mp (by simpa using hroots_bnd _ h_idx_pos)
    rw [neg_root_zmod _ hroots_bnd_at]
    have h_root_val : ((roots[2 * s - j2]'h_idx_pos).toNat : ZMod mod32.toNat) =
        (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (s - j2))
          * (montR1.toNat : ZMod mod32.toNat) := by
      apply ntt_roots_correct_at roots hroots len (s - j2) (2 * s - j2)
      · omega
      · exact dvd_of_mul_left_dvd hlen_dvd
      · omega
      · rw [hlen,
          show 2 * s / 2 = s from Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]
        omega
    rw [h_root_val]
    have h_neg : -((primRoot.toNat : ZMod mod32.toNat) ^
          ((mod64.toNat - 1) / len * (s - j2)) * (montR1.toNat : ZMod mod32.toNat))
        = (primRoot.toNat : ZMod mod32.toNat) ^
          ((mod64.toNat - 1) / len * (s - j2) + (mod64.toNat - 1) / 2)
          * (montR1.toNat : ZMod mod32.toNat) := by
      rw [pow_add, prim_root_half_eq_neg_one]; ring
    rw [h_neg, twiddle_neg_exp_identity (mod64.toNat - 1) len s j2 hlen
      (dvd_trans hlen_dvd hN_dvd) hj2]
  · rw [if_neg hj2_pos]
    have hj2_zero : j2 = 0 := by omega
    rw [vector_getD_eq_getElem roots _ h_idx_zero 0]
    have h_root_val : ((roots[s]'h_idx_zero).toNat : ZMod mod32.toNat) =
        (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * 0)
          * (montR1.toNat : ZMod mod32.toNat) := by
      apply ntt_roots_correct_at roots hroots len 0 s
      · omega
      · exact dvd_of_mul_left_dvd hlen_dvd
      · omega
      · rw [hlen,
          show 2 * s / 2 = s from Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]
        omega
    rw [h_root_val, hj2_zero]
    have h_len_dvd : len ∣ mod64.toNat - 1 :=
      dvd_trans (dvd_of_mul_left_dvd hlen_dvd) hN_dvd
    have hprim_pow : (primRoot.toNat : ZMod mod32.toNat) ^ (mod64.toNat - 1) = 1 := by
      rw [mod32_eq_mod]; exact ZMod.pow_card_sub_one_eq_one prim_root_ne_zero_ZMod
    rw [show len - 0 = len from by omega, mul_zero, pow_zero,
        show (mod64.toNat - 1) / len * len = mod64.toNat - 1 from
          Nat.div_mul_cancel h_len_dvd,
        hprim_pow, one_mul]

-- Helper: ZMod value of inverse `t2` twiddle.
lemma inverse_t2_zmod {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots) (hroots_bnd : roots.all (· < mod32))
    (s len j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (h_idx_pos : j2 > 0 → 2 * len - j2 < N)
    (h_idx_pos_eq : 2 * len - j2 = len + (len - j2))
    (h_idx_zero : len < N) :
    ((if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0
      else roots.getD len 0).toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - j2)) * (montR1.toNat : ZMod mod32.toNat) := by
  have hlen_pos : len > 0 := by omega
  by_cases hj2_pos : j2 > 0
  · rw [if_pos hj2_pos]
    have h_idx_pos' := h_idx_pos hj2_pos
    rw [vector_getD_eq_getElem roots _ h_idx_pos' 0]
    have hroots_bnd_at : (roots[2 * len - j2]'h_idx_pos').toNat < mod32.toNat := by
      rw [Vector.all_eq_true] at hroots_bnd
      exact UInt32.lt_iff_toNat_lt.mp (by simpa using hroots_bnd _ h_idx_pos')
    rw [neg_root_zmod _ hroots_bnd_at]
    have h_root_val : ((roots[2 * len - j2]'h_idx_pos').toNat : ZMod mod32.toNat) =
        (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * (len - j2))
          * (montR1.toNat : ZMod mod32.toNat) := by
      apply ntt_roots_correct_at roots hroots (2 * len) (len - j2) (2 * len - j2)
      · omega
      · exact hlen_dvd
      · omega
      · rw [show 2 * len / 2 = len from
              Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]
        omega
    rw [h_root_val]
    have h_neg : -((primRoot.toNat : ZMod mod32.toNat) ^
          ((mod64.toNat - 1) / (2 * len) * (len - j2))
          * (montR1.toNat : ZMod mod32.toNat))
        = (primRoot.toNat : ZMod mod32.toNat) ^
          ((mod64.toNat - 1) / (2 * len) * (len - j2) + (mod64.toNat - 1) / 2)
          * (montR1.toNat : ZMod mod32.toNat) := by
      rw [pow_add, prim_root_half_eq_neg_one]; ring
    rw [h_neg, twiddle_neg_exp_identity_t2 (mod64.toNat - 1) len j2
      (dvd_trans hlen_dvd hN_dvd) (by decide) (by omega)]
  · rw [if_neg hj2_pos]
    have hj2_zero : j2 = 0 := by omega
    rw [vector_getD_eq_getElem roots _ h_idx_zero 0]
    have h_root_val : ((roots[len]'h_idx_zero).toNat : ZMod mod32.toNat) =
        (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * 0)
          * (montR1.toNat : ZMod mod32.toNat) := by
      apply ntt_roots_correct_at roots hroots (2 * len) 0 len
      · omega
      · exact hlen_dvd
      · omega
      · rw [show 2 * len / 2 = len from
              Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]
        omega
    rw [h_root_val, hj2_zero]
    have h_dvd : 2 * len ∣ mod64.toNat - 1 := dvd_trans hlen_dvd hN_dvd
    have hprim_pow : (primRoot.toNat : ZMod mod32.toNat) ^ (mod64.toNat - 1) = 1 := by
      rw [mod32_eq_mod]; exact ZMod.pow_card_sub_one_eq_one prim_root_ne_zero_ZMod
    rw [show 2 * len - 0 = 2 * len from by omega, mul_zero, pow_zero,
        show (mod64.toNat - 1) / (2 * len) * (2 * len) = mod64.toNat - 1 from
          Nat.div_mul_cancel h_dvd,
        hprim_pow, one_mul]

-- Helper: ZMod value of inverse `t3` twiddle (always negated, no j2 case split).
lemma inverse_t3_zmod {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots) (hroots_bnd : roots.all (· < mod32))
    (s len j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (h_idx : 2 * len - j2 - s < N)
    (h_idx_eq : 2 * len - j2 - s = len + (s - j2)) :
    ((mod32 - roots.getD (2 * len - j2 - s) 0).toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - s - j2)) * (montR1.toNat : ZMod mod32.toNat) := by
  rw [vector_getD_eq_getElem roots _ h_idx 0]
  have hroots_bnd_at : (roots[2 * len - j2 - s]'h_idx).toNat < mod32.toNat := by
    rw [Vector.all_eq_true] at hroots_bnd
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using hroots_bnd _ h_idx)
  rw [neg_root_zmod _ hroots_bnd_at]
  have hlen_pos : len > 0 := by omega
  have h_root_val : ((roots[2 * len - j2 - s]'h_idx).toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * (s - j2))
        * (montR1.toNat : ZMod mod32.toNat) := by
    apply ntt_roots_correct_at roots hroots (2 * len) (s - j2) (2 * len - j2 - s)
    · omega
    · exact hlen_dvd
    · rw [show 2 * len / 2 = len from
            Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]
      omega
    · rw [show 2 * len / 2 = len from
            Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]
      omega
  rw [h_root_val]
  have h_neg : -((primRoot.toNat : ZMod mod32.toNat) ^
        ((mod64.toNat - 1) / (2 * len) * (s - j2))
        * (montR1.toNat : ZMod mod32.toNat))
      = (primRoot.toNat : ZMod mod32.toNat) ^
        ((mod64.toNat - 1) / (2 * len) * (s - j2) + (mod64.toNat - 1) / 2)
        * (montR1.toNat : ZMod mod32.toNat) := by
    rw [pow_add, prim_root_half_eq_neg_one]; ring
  rw [h_neg, twiddle_neg_exp_identity_t3 (mod64.toNat - 1) len s j2
    hlen (dvd_trans hlen_dvd hN_dvd) hj2]

/-- Helper: bound on inverse t1 value: `t1.toNat < mod32.toNat`. -/
lemma inverse_t1_bound {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots) (hroots_bnd : roots.all (· < mod32))
    (s len j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N)
    (hj2 : j2 < s)
    (h_idx_pos : 2 * s - j2 < N)
    (h_idx_pos_eq : 2 * s - j2 = s + (s - j2))
    (h_idx_zero : s < N) :
    (if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0
      else roots.getD s 0).toNat < mod32.toNat := by
  by_cases hj2_pos : j2 > 0
  · rw [if_pos hj2_pos]
    rw [vector_getD_eq_getElem roots _ h_idx_pos 0]
    apply inverse_twiddle_bound roots hroots hroots_bnd len (s - j2)
      (by omega) (dvd_of_mul_left_dvd hlen_dvd) (by omega) _ h_idx_pos
    rw [hlen,
      show 2 * s / 2 = s from Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]
    omega
  · rw [if_neg hj2_pos]
    rw [vector_getD_eq_getElem roots _ h_idx_zero 0]
    rw [Vector.all_eq_true] at hroots_bnd
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using hroots_bnd _ h_idx_zero)

/-- Helper: bound on inverse t2 value: `t2.toNat < mod32.toNat`. -/
lemma inverse_t2_bound {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots) (hroots_bnd : roots.all (· < mod32))
    (len j2 : ℕ) (hlen_pos : len > 0)
    (hlen_dvd : 2 * len ∣ N)
    (hj2 : j2 < len)
    (h_idx_pos : j2 > 0 → 2 * len - j2 < N)
    (h_idx_pos_eq : 2 * len - j2 = len + (len - j2))
    (h_idx_zero : len < N) :
    (if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0
      else roots.getD len 0).toNat < mod32.toNat := by
  by_cases hj2_pos : j2 > 0
  · rw [if_pos hj2_pos]
    have h_idx_pos' := h_idx_pos hj2_pos
    rw [vector_getD_eq_getElem roots _ h_idx_pos' 0]
    apply inverse_twiddle_bound roots hroots hroots_bnd (2 * len) (len - j2)
      (by omega) hlen_dvd _ _ h_idx_pos'
    · rw [show 2 * len / 2 = len from
        Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]; omega
    · rw [show 2 * len / 2 = len from
        Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]; omega
  · rw [if_neg hj2_pos]
    rw [vector_getD_eq_getElem roots _ h_idx_zero 0]
    rw [Vector.all_eq_true] at hroots_bnd
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using hroots_bnd _ h_idx_zero)

/-- Helper: bound on inverse t3 value: `t3.toNat < mod32.toNat`. -/
lemma inverse_t3_bound {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots) (hroots_bnd : roots.all (· < mod32))
    (s len j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N)
    (hj2 : j2 < s)
    (h_idx : 2 * len - j2 - s < N)
    (h_idx_eq : 2 * len - j2 - s = len + (s - j2)) :
    (mod32 - roots.getD (2 * len - j2 - s) 0).toNat < mod32.toNat := by
  rw [vector_getD_eq_getElem roots _ h_idx 0]
  have hlen_pos : len > 0 := by omega
  apply inverse_twiddle_bound roots hroots hroots_bnd (2 * len) (s - j2)
    (by omega) hlen_dvd _ _ h_idx
  · rw [show 2 * len / 2 = len from
      Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]; omega
  · rw [show 2 * len / 2 = len from
      Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]; omega

private lemma uint64_two_mul_sub (x j2 : UInt64)
    (hj2 : j2.toNat < x.toNat) (h2x : 2 * x.toNat < 2 ^ 64) :
    (2 * x - j2).toNat = x.toNat + (x.toNat - j2.toNat) := by
  rw [UInt64.toNat_sub, UInt64.toNat_mul]
  have h2 : (2 : UInt64).toNat = 2 := by decide
  rw [h2, Nat.mod_eq_of_lt h2x]
  rw [show 2 ^ 64 - j2.toNat + 2 * x.toNat = 2 ^ 64 + (x.toNat + (x.toNat - j2.toNat)) by omega]
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

-- The ZMod correctness proof for inverse butterfly4 at position 0 requires many rewrites.
lemma butterfly4_inverse_ZMod_pos0 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N) :
    ((butterfly4 a true roots s len i2 j2)[i2 + j2]'hbnd0).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
        (a[i2 + j2 + s]'hbnd1).toNat +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - j2)) *
        ((a[i2 + len + j2]'hbnd2).toNat +
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have hs_pos : s > 0 := by omega
  have hlen_pos : len > 0 := by omega
  have hN_pos : N > 0 := by omega
  have h2len_le : 2 * len ≤ N := Nat.le_of_dvd hN_pos hlen_dvd
  have h_idx_2s_minus : 2 * s - j2 < N := by omega
  have h_idx_2s_minus_eq : 2 * s - j2 = s + (s - j2) := by omega
  have h_idx_2len_minus_eq : 2 * len - j2 = len + (len - j2) := by omega
  have h_idx_s : s < N := by omega
  have h_idx_len : len < N := by omega
  have hne10 : i2 + j2 + s ≠ i2 + j2 := by omega
  have hne20 : i2 + len + j2 ≠ i2 + j2 := by omega
  have hne30 : i2 + len + j2 + s ≠ i2 + j2 := by omega
  rw [butterfly4_inverse_getElem_pos0 roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3 hne10 hne20 hne30]
  set t1 : UInt32 :=
    if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0 with ht1_def
  set t2 : UInt32 :=
    if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0 else roots.getD len 0 with ht2_def
  have ht1_bnd : t1.toNat < mod32.toNat := by
    rw [ht1_def]
    exact inverse_t1_bound roots hroots hroots_bnd s len j2 hlen hlen_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have h_idx_2len_minus_cond : j2 > 0 → 2 * len - j2 < N := by intro; omega
  have ht2_bnd : t2.toNat < mod32.toNat := by
    rw [ht2_def]
    exact inverse_t2_bound roots hroots hroots_bnd len j2 hlen_pos hlen_dvd (by omega)
      h_idx_2len_minus_cond h_idx_2len_minus_eq h_idx_len
  have ht1_zmod : (t1.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2))
        * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht1_def]
    exact inverse_t1_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have ht2_zmod : (t2.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - j2)) * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht2_def]
    exact inverse_t2_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2len_minus_cond h_idx_2len_minus_eq h_idx_len
  have h_a_all : ∀ idx (hidx : idx < N), (a[idx]'hidx).toNat < mod32.toNat := by
    rw [Vector.all_eq_true] at ha
    intro idx hidx
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using ha _ hidx)
  have ha0 := h_a_all _ hbnd0
  have ha1 := h_a_all _ hbnd1
  have ha2 := h_a_all _ hbnd2
  have ha3 := h_a_all _ hbnd3
  have h_mont_a1_t1 := mont_mul_lt_of_left (a[i2 + j2 + s]'hbnd1) t1 ha1
  have h_mont_a3_t1 := mont_mul_lt_of_left (a[i2 + len + j2 + s]'hbnd3) t1 ha3
  have h_P_bnd := addmod32_lt _ _ ha0 h_mont_a1_t1
  have h_R_bnd := addmod32_lt _ _ ha2 h_mont_a3_t1
  have h_t2R_bnd := mont_mul_lt_of_right t2 _ h_R_bnd
  rw [addmod32_ZMod _ _ h_P_bnd h_t2R_bnd,
      addmod32_ZMod _ _ ha0 h_mont_a1_t1,
      mont_mul_ZMod _ _ ha1 ht1_bnd,
      mont_mul_ZMod _ _ ht2_bnd h_R_bnd,
      addmod32_ZMod _ _ ha2 h_mont_a3_t1,
      mont_mul_ZMod _ _ ha3 ht1_bnd,
      ht1_zmod, ht2_zmod,
      MONT_R1_ZMod]
  simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
    mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
  ring

-- The ZMod correctness proof for inverse butterfly4 at position 2 requires many rewrites.
lemma butterfly4_inverse_ZMod_pos2 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N) :
    ((butterfly4 a true roots s len i2 j2)[i2 + len + j2]'hbnd2).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
        (a[i2 + j2 + s]'hbnd1).toNat -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - j2)) *
        ((a[i2 + len + j2]'hbnd2).toNat +
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have hs_pos : s > 0 := by omega
  have hlen_pos : len > 0 := by omega
  have hN_pos : N > 0 := by omega
  have h2len_le : 2 * len ≤ N := Nat.le_of_dvd hN_pos hlen_dvd
  have h_idx_2s_minus : 2 * s - j2 < N := by omega
  have h_idx_2s_minus_eq : 2 * s - j2 = s + (s - j2) := by omega
  have h_idx_2len_minus_eq : 2 * len - j2 = len + (len - j2) := by omega
  have h_idx_2len_minus_cond : j2 > 0 → 2 * len - j2 < N := by intro; omega
  have h_idx_s : s < N := by omega
  have h_idx_len : len < N := by omega
  have hne12 : i2 + j2 + s ≠ i2 + len + j2 := by omega
  have hne32 : i2 + len + j2 + s ≠ i2 + len + j2 := by omega
  rw [butterfly4_inverse_getElem_pos2 roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3 hne12 hne32]
  set t1 : UInt32 :=
    if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0 with ht1_def
  set t2 : UInt32 :=
    if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0 else roots.getD len 0 with ht2_def
  have ht1_bnd : t1.toNat < mod32.toNat := by
    rw [ht1_def]
    exact inverse_t1_bound roots hroots hroots_bnd s len j2 hlen hlen_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have ht2_bnd : t2.toNat < mod32.toNat := by
    rw [ht2_def]
    exact inverse_t2_bound roots hroots hroots_bnd len j2 hlen_pos hlen_dvd (by omega)
      h_idx_2len_minus_cond h_idx_2len_minus_eq h_idx_len
  have ht1_zmod : (t1.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2))
        * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht1_def]
    exact inverse_t1_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have ht2_zmod : (t2.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - j2)) * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht2_def]
    exact inverse_t2_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2len_minus_cond h_idx_2len_minus_eq h_idx_len
  have h_a_all : ∀ idx (hidx : idx < N), (a[idx]'hidx).toNat < mod32.toNat := by
    rw [Vector.all_eq_true] at ha
    intro idx hidx
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using ha _ hidx)
  have ha0 := h_a_all _ hbnd0
  have ha1 := h_a_all _ hbnd1
  have ha2 := h_a_all _ hbnd2
  have ha3 := h_a_all _ hbnd3
  have h_mont_a1_t1 := mont_mul_lt_of_left (a[i2 + j2 + s]'hbnd1) t1 ha1
  have h_mont_a3_t1 := mont_mul_lt_of_left (a[i2 + len + j2 + s]'hbnd3) t1 ha3
  have h_P_bnd := addmod32_lt _ _ ha0 h_mont_a1_t1
  have h_R_bnd := addmod32_lt _ _ ha2 h_mont_a3_t1
  have h_t2R_bnd := mont_mul_lt_of_right t2 _ h_R_bnd
  rw [submod32_ZMod _ _ h_P_bnd h_t2R_bnd,
      addmod32_ZMod _ _ ha0 h_mont_a1_t1,
      mont_mul_ZMod _ _ ha1 ht1_bnd,
      mont_mul_ZMod _ _ ht2_bnd h_R_bnd,
      addmod32_ZMod _ _ ha2 h_mont_a3_t1,
      mont_mul_ZMod _ _ ha3 ht1_bnd,
      ht1_zmod, ht2_zmod,
      MONT_R1_ZMod]
  simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
    mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
  ring

-- The ZMod correctness proof for inverse butterfly4 at position 1 requires many rewrites.
lemma butterfly4_inverse_ZMod_pos1 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N) :
    ((butterfly4 a true roots s len i2 j2)[i2 + j2 + s]'hbnd1).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
        (a[i2 + j2 + s]'hbnd1).toNat +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - s - j2)) *
        ((a[i2 + len + j2]'hbnd2).toNat -
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have hs_pos : s > 0 := by omega
  have hlen_pos : len > 0 := by omega
  have hN_pos : N > 0 := by omega
  have h2len_le : 2 * len ≤ N := Nat.le_of_dvd hN_pos hlen_dvd
  have h_idx_2s_minus : 2 * s - j2 < N := by omega
  have h_idx_2s_minus_eq : 2 * s - j2 = s + (s - j2) := by omega
  have h_idx_2len_minus_s_eq : 2 * len - j2 - s = len + (s - j2) := by omega
  have h_idx_2len_minus_s : 2 * len - j2 - s < N := by omega
  have h_idx_s : s < N := by omega
  have hne31 : i2 + len + j2 + s ≠ i2 + j2 + s := by omega
  rw [butterfly4_inverse_getElem_pos1 roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3 hne31]
  set t1 : UInt32 :=
    if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0 with ht1_def
  set t3 : UInt32 := mod32 - roots.getD (2 * len - j2 - s) 0 with ht3_def
  have ht1_bnd : t1.toNat < mod32.toNat := by
    rw [ht1_def]
    exact inverse_t1_bound roots hroots hroots_bnd s len j2 hlen hlen_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have ht3_bnd : t3.toNat < mod32.toNat := by
    rw [ht3_def]
    exact inverse_t3_bound roots hroots hroots_bnd s len j2 hlen hlen_dvd hj2
      h_idx_2len_minus_s h_idx_2len_minus_s_eq
  have ht1_zmod : (t1.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2))
        * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht1_def]
    exact inverse_t1_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have ht3_zmod : (t3.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - s - j2)) * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht3_def]
    exact inverse_t3_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2len_minus_s h_idx_2len_minus_s_eq
  have h_a_all : ∀ idx (hidx : idx < N), (a[idx]'hidx).toNat < mod32.toNat := by
    rw [Vector.all_eq_true] at ha
    intro idx hidx
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using ha _ hidx)
  have ha0 := h_a_all _ hbnd0
  have ha1 := h_a_all _ hbnd1
  have ha2 := h_a_all _ hbnd2
  have ha3 := h_a_all _ hbnd3
  have h_mont_a1_t1 := mont_mul_lt_of_left (a[i2 + j2 + s]'hbnd1) t1 ha1
  have h_mont_a3_t1 := mont_mul_lt_of_left (a[i2 + len + j2 + s]'hbnd3) t1 ha3
  have h_Q_bnd := submod32_lt _ _ ha0 h_mont_a1_t1
  have h_S_bnd := submod32_lt _ _ ha2 h_mont_a3_t1
  have h_t3S_bnd := mont_mul_lt_of_right t3 _ h_S_bnd
  rw [addmod32_ZMod _ _ h_Q_bnd h_t3S_bnd,
      submod32_ZMod _ _ ha0 h_mont_a1_t1,
      mont_mul_ZMod _ _ ha1 ht1_bnd,
      mont_mul_ZMod _ _ ht3_bnd h_S_bnd,
      submod32_ZMod _ _ ha2 h_mont_a3_t1,
      mont_mul_ZMod _ _ ha3 ht1_bnd,
      ht1_zmod, ht3_zmod,
      MONT_R1_ZMod]
  simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
    mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
  ring

-- The ZMod correctness proof for inverse butterfly4 at position 3 requires many rewrites.
lemma butterfly4_inverse_ZMod_pos3 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N) :
    ((butterfly4 a true roots s len i2 j2)[i2 + len + j2 + s]'hbnd3).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
        (a[i2 + j2 + s]'hbnd1).toNat -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - s - j2)) *
        ((a[i2 + len + j2]'hbnd2).toNat -
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have hs_pos : s > 0 := by omega
  have hlen_pos : len > 0 := by omega
  have hN_pos : N > 0 := by omega
  have h2len_le : 2 * len ≤ N := Nat.le_of_dvd hN_pos hlen_dvd
  have h_idx_2s_minus : 2 * s - j2 < N := by omega
  have h_idx_2s_minus_eq : 2 * s - j2 = s + (s - j2) := by omega
  have h_idx_2len_minus_s_eq : 2 * len - j2 - s = len + (s - j2) := by omega
  have h_idx_2len_minus_s : 2 * len - j2 - s < N := by omega
  have h_idx_s : s < N := by omega
  rw [butterfly4_inverse_getElem_pos3 roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3]
  set t1 : UInt32 :=
    if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0 with ht1_def
  set t3 : UInt32 := mod32 - roots.getD (2 * len - j2 - s) 0 with ht3_def
  have ht1_bnd : t1.toNat < mod32.toNat := by
    rw [ht1_def]
    exact inverse_t1_bound roots hroots hroots_bnd s len j2 hlen hlen_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have ht3_bnd : t3.toNat < mod32.toNat := by
    rw [ht3_def]
    exact inverse_t3_bound roots hroots hroots_bnd s len j2 hlen hlen_dvd hj2
      h_idx_2len_minus_s h_idx_2len_minus_s_eq
  have ht1_zmod : (t1.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2))
        * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht1_def]
    exact inverse_t1_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have ht3_zmod : (t3.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - s - j2)) * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht3_def]
    exact inverse_t3_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2len_minus_s h_idx_2len_minus_s_eq
  have h_a_all : ∀ idx (hidx : idx < N), (a[idx]'hidx).toNat < mod32.toNat := by
    rw [Vector.all_eq_true] at ha
    intro idx hidx
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using ha _ hidx)
  have ha0 := h_a_all _ hbnd0
  have ha1 := h_a_all _ hbnd1
  have ha2 := h_a_all _ hbnd2
  have ha3 := h_a_all _ hbnd3
  have h_mont_a1_t1 := mont_mul_lt_of_left (a[i2 + j2 + s]'hbnd1) t1 ha1
  have h_mont_a3_t1 := mont_mul_lt_of_left (a[i2 + len + j2 + s]'hbnd3) t1 ha3
  have h_Q_bnd := submod32_lt _ _ ha0 h_mont_a1_t1
  have h_S_bnd := submod32_lt _ _ ha2 h_mont_a3_t1
  have h_t3S_bnd := mont_mul_lt_of_right t3 _ h_S_bnd
  rw [submod32_ZMod _ _ h_Q_bnd h_t3S_bnd,
      submod32_ZMod _ _ ha0 h_mont_a1_t1,
      mont_mul_ZMod _ _ ha1 ht1_bnd,
      mont_mul_ZMod _ _ ht3_bnd h_S_bnd,
      submod32_ZMod _ _ ha2 h_mont_a3_t1,
      mont_mul_ZMod _ _ ha3 ht1_bnd,
      ht1_zmod, ht3_zmod,
      MONT_R1_ZMod]
  simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
    mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
  ring

/-- Bundle the four inverse-butterfly position results into a single conjunction,
    mirroring `butterfly4_forward_ZMod_combined`. -/
lemma butterfly4_inverse_ZMod_combined {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N) :
    let τ₁ : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2))
    let τ₂ : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * (2 * len - j2))
    let τ₃ : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - s - j2))
    let r  := butterfly4 a true roots s len i2 j2
    let A₀ := ((a[(i2 + j2)]'hbnd0).toNat       : ZMod mod32.toNat)
    let A₁ := ((a[(i2 + j2 + s)]'hbnd1).toNat   : ZMod mod32.toNat)
    let A₂ := ((a[(i2 + len + j2)]'hbnd2).toNat : ZMod mod32.toNat)
    let A₃ := ((a[(i2 + len + j2 + s)]'hbnd3).toNat : ZMod mod32.toNat)
    ((r[(i2 + j2)]'hbnd0).toNat           : ZMod mod32.toNat) =
        A₀ + τ₁ * A₁ + τ₂ * (A₂ + τ₁ * A₃) ∧
    ((r[(i2 + len + j2)]'hbnd2).toNat     : ZMod mod32.toNat) =
        A₀ + τ₁ * A₁ - τ₂ * (A₂ + τ₁ * A₃) ∧
    ((r[(i2 + j2 + s)]'hbnd1).toNat       : ZMod mod32.toNat) =
        A₀ - τ₁ * A₁ + τ₃ * (A₂ - τ₁ * A₃) ∧
    ((r[(i2 + len + j2 + s)]'hbnd3).toNat : ZMod mod32.toNat) =
        A₀ - τ₁ * A₁ - τ₃ * (A₂ - τ₁ * A₃) := by
  simp only []
  exact ⟨butterfly4_inverse_ZMod_pos0 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hN_dvd hj2 hbnd0 hbnd1 hbnd2 hbnd3,
  butterfly4_inverse_ZMod_pos2 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hN_dvd hj2 hbnd0 hbnd1 hbnd2 hbnd3,
  butterfly4_inverse_ZMod_pos1 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hN_dvd hj2 hbnd0 hbnd1 hbnd2 hbnd3,
  butterfly4_inverse_ZMod_pos3 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hN_dvd hj2 hbnd0 hbnd1 hbnd2 hbnd3⟩
