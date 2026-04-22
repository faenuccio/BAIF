/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Funs
import Mathlib.Tactic.IntervalCases

/-! # Reduce -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `reduce` -/

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce

@[step]
theorem LOW_51_BIT_MASK_spec :
    LOW_51_BIT_MASK ⦃ result => result.val = 2^51 - 1 ⦄ := by
  unfold LOW_51_BIT_MASK
  step*

end curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

-- set_option profiler

lemma foo1 (d : U64) : (d : ℕ) >>> 51 * (19#u64 : ℕ) ≤ U64.max := by
  scalar_tac

lemma foo2 (i j k : U64) (hk : k = (2 ^ 51 - 1 : ℕ)) :
    (((i &&& k) : U64) : ℕ) + ((j : ℕ) >>> 51) * 19 ≤ U64.max := by
  simp only [UScalar.val_and, hk, Nat.and_two_pow_sub_one_eq_mod]
  scalar_tac

lemma foo3 (i j k : U64) (hk : k = (2 ^ 51 - 1 : ℕ)) :
    (((i &&& k) : U64) : ℕ) + ((j : ℕ) >>> 51) ≤ U64.max := by
  simp only [UScalar.val_and, hk, Nat.and_two_pow_sub_one_eq_mod]
  scalar_tac

lemma foo4 : U64.max = 2^64 - 1 := by scalar_tac

-- grind_pattern foo2 => ((j : ℕ) >>> 51)

set_option maxHeartbeats 500000 in -- heavy step, scalar_tac and simp_all's
/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.reduce`**:
- All the limbs of the result are small, ≤ 2^(51 + ε)
- The result is equal to the input mod p.
- The result value is < 2p. -/
@[step]
theorem reduce_spec (limbs : Array U64 5#usize) :
    reduce limbs ⦃ (result : FieldElement51) =>
      (∀ i < 5, result[i]!.val < 2 ^ 52) ∧
      Field51_as_Nat limbs ≡ Field51_as_Nat result [MOD p] ∧
      Field51_as_Nat result < 2 * p ⦄ := by
  -- have foo4 := foo4
  unfold reduce
  step*
  · rw [c4_post1]
    apply foo1
  · grw [← foo2 i i4 i5 (by assumption)]
    grind
  · grw [← foo3 i8 i i5 (by assumption)]
    grind
  · grw [← foo3 i10 i1 i5 (by assumption)]
    grind
  · grw [← foo3 i12 i2 i5 (by assumption)]
    grind
  · grw [← foo3 i14 i3 i5 (by assumption)]
    gcongr
    · simp [i24_post, limbs9_post, limbs8_post, limbs7_post, limbs6_post,
        limbs5_post]
      grind
    grind
  -- A ∧ B: limb bounds ∧ ModEq
  constructor
  · intro i _
    interval_cases i
    all_goals simp only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
        UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, Nat.one_lt_ofNat, Nat.reduceLT,
        Nat.lt_add_one, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod, Array.set_val_eq,
        List.length_set, ne_eq, zero_ne_one, not_false_eq_true, List.getElem_set_ne,
        OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_zero, one_ne_zero,
        List.getElem_set_self, OfNat.ofNat_ne_one, Nat.succ_ne_self, Nat.ofNat_pos,
        Array.getElem!_Nat_eq]; scalar_tac
  · simp only [Nat.ModEq, Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
      Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero,
      List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem?_pos,
      Option.getD_some, one_mul, mul_one, Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceLT,
      Nat.lt_add_one, p, Array.set_val_eq, List.length_set, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, List.getElem_set_ne, one_ne_zero, List.getElem_set_self, getElem!_pos,
      UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod, OfNat.ofNat_ne_one, zero_ne_one,
      Nat.reduceEqDiff, Nat.succ_ne_self, OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat, limbs10_post,
      limbs9_post, limbs8_post, limbs7_post, limbs6_post, limbs5_post, limbs4_post, limbs3_post,
      limbs2_post, limbs1_post, i17_post, i16_post, i6_post1, i_post, i5_post, i15_post, c4_post1,
      i4_post, i19_post, i18_post, i8_post1, i7_post, c0_post1, i21_post, i20_post, i10_post1,
      i9_post, c1_post1, i1_post, i23_post, i22_post, i12_post1, i11_post, c2_post1, i2_post,
      i25_post, i24_post, i14_post1, i13_post, c3_post1, i3_post]; scalar_tac

end curve25519_dalek.backend.serial.u64.field.FieldElement51
