/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Codes.GolayDistribution
import Mathlib.Algebra.Polynomial.Coeff

namespace Atlas.Codes
open scoped BigOperators Polynomial

noncomputable def hexEnumerator : ℕ[X] := ∑ w : hexacode, Polynomial.X ^ hammingNorm w.val
noncomputable def golayEnumerator : ℕ[X] := ∑ w : golay, Polynomial.X ^ hammingNorm w.val
noncomputable def evenCosetEnumerator : ℕ[X] := ∑ w : C0, Polynomial.X ^ hammingNorm w.val
noncomputable def oddCosetEnumerator : ℕ[X] := ∑ w : C0, Polynomial.X ^ hammingNorm (w.val + eta)

theorem hexEnumerator_coeff (k : ℕ) : hexEnumerator.coeff k = hexWeightCount k := by
  classical
  simp only [hexEnumerator, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow,
    hexWeightCount, Finset.card_filter, eq_comm]

theorem golayEnumerator_coeff (k : ℕ) : golayEnumerator.coeff k = golayWeightCount k := by
  classical
  simp only [golayEnumerator, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow,
    golayWeightCount, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, eq_comm]

theorem evenCosetEnumerator_coeff (k : ℕ) : evenCosetEnumerator.coeff k = evenCosetCount k := by
  classical
  simp only [evenCosetEnumerator, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow,
    evenCosetCount, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, eq_comm]

theorem oddCosetEnumerator_coeff (k : ℕ) : oddCosetEnumerator.coeff k = oddCosetCount k := by
  classical
  simp only [oddCosetEnumerator, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow,
    oddCosetCount, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, eq_comm]

theorem hexEnumerator_eq : hexEnumerator = 1 + 45 * Polynomial.X^4 + 18 * Polynomial.X^6 := by
  ext k
  rw [hexEnumerator_coeff, hexacode_weight_distribution]
  simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_natCast_mul,
    Polynomial.coeff_X_pow]
  split_ifs <;> simp_all

theorem golayEnumerator_eq : golayEnumerator = 1 + 759 * Polynomial.X^8 +
    2576 * Polynomial.X^12 + 759 * Polynomial.X^16 + Polynomial.X^24 := by
  ext k
  rw [golayEnumerator_coeff, golay_weight_distribution]
  simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_natCast_mul,
    Polynomial.coeff_X_pow]
  split_ifs <;> simp_all

theorem evenCosetEnumerator_eq : evenCosetEnumerator = 1 + 375 * Polynomial.X^8 +
    1296 * Polynomial.X^12 + 375 * Polynomial.X^16 + Polynomial.X^24 := by
  ext k
  rw [evenCosetEnumerator_coeff, even_coset_distribution]
  simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_natCast_mul,
    Polynomial.coeff_X_pow]
  split_ifs <;> simp_all

theorem oddCosetEnumerator_eq : oddCosetEnumerator = 384 * Polynomial.X^8 +
    1280 * Polynomial.X^12 + 384 * Polynomial.X^16 := by
  ext k
  rw [oddCosetEnumerator_coeff, odd_coset_distribution]
  simp only [Polynomial.coeff_add, Polynomial.coeff_natCast_mul, Polynomial.coeff_X_pow]
  split_ifs <;> simp_all

theorem golay_homogeneous_enumerator {R : Type*} [CommSemiring R] (X Y : R) :
    (∑ w : golay, X ^ (24 - hammingNorm w.val) * Y ^ hammingNorm w.val) =
      X^24 + 759 * X^16 * Y^8 + 2576 * X^12 * Y^12 + 759 * X^8 * Y^16 + Y^24 := by
  classical
  have he (w : golay) : X ^ (24 - hammingNorm w.val) * Y ^ hammingNorm w.val =
      (if hammingNorm w.val = 0 then X^24 else 0) +
      (if hammingNorm w.val = 8 then X^16 * Y^8 else 0) +
      (if hammingNorm w.val = 12 then X^12 * Y^12 else 0) +
      (if hammingNorm w.val = 16 then X^8 * Y^16 else 0) +
      (if hammingNorm w.val = 24 then Y^24 else 0) := by
    rcases golay_weights w with h | h | h | h | h <;> simp [h]
  have hs := congrArg (fun f : golay → R => ∑ w, f w) (funext he)
  simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
    add_zero, Finset.sum_const] at hs
  have hc (k : ℕ) : (Finset.univ.filter (fun w : golay => hammingNorm w.val = k)).card =
      golayWeightCount k := by
    rw [golayWeightCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [hc, golay_weight_distribution] at hs
  norm_num [nsmul_eq_mul] at hs
  simpa only [mul_assoc] using hs

end Atlas.Codes
