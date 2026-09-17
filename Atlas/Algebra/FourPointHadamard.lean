import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Atlas.Algebra
open scoped BigOperators

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- The reflection matrix J-2I on four actual labels. -/
def fourPointHadamardEntry (i j : ι) : R := if i = j then -1 else 1

theorem fourPointHadamard_gram [Fintype ι] (hc : Fintype.card ι = 4) (i k : ι) :
    (∑ j, fourPointHadamardEntry (R := R) i j * fourPointHadamardEntry k j) =
      if i = k then 4 else 0 := by
  classical
  by_cases hik : i = k
  · subst k
    have hp (j : ι) : fourPointHadamardEntry (R := R) i j * fourPointHadamardEntry i j = 1 := by
      unfold fourPointHadamardEntry
      split_ifs <;> ring
    simp only [hp, Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul, mul_one,
      ite_eq_left rfl]
    norm_num
  · have hp (j : ι) : fourPointHadamardEntry (R := R) i j * fourPointHadamardEntry k j =
        1 - 2 * (if j = i then (1 : R) else 0) - 2 * (if j = k then (1 : R) else 0) := by
      by_cases hji : j = i
      · subst j
        simp only [fourPointHadamardEntry, ite_true, ite_eq_left rfl, ite_eq_right hik,
          ite_eq_right (Ne.symm hik)]
        ring
      · by_cases hjk : j = k
        · subst j
          simp only [fourPointHadamardEntry, ite_true, ite_eq_left rfl, ite_eq_right hik,
            ite_eq_right (Ne.symm hik)]
          ring
        · simp only [fourPointHadamardEntry, ite_true, ite_eq_right hji, ite_eq_right hjk,
            ite_eq_right (Ne.symm hji), ite_eq_right (Ne.symm hjk)]
          ring
    simp only [hp, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
      hc, nsmul_eq_mul, mul_one, ite_eq_right hik]
    ring

/-- The source four-character Walsh matrix, in its displayed order. -/
def walshFourMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1]

/-- Explicit row and column sign changes identify J-2I with the source H4. -/
theorem walshFourMatrix_eq_signed_fourPoint (i j : Fin 4) :
    walshFourMatrix i j = (if i = 0 then (1 : ℤ) else -1) *
      fourPointHadamardEntry i j * (if j = 0 then -1 else 1) := by
  fin_cases i <;> fin_cases j <;> norm_num [walshFourMatrix, fourPointHadamardEntry]

end Atlas.Algebra
