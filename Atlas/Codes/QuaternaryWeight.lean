import Atlas.Codes.QuaternaryEvenness

/-! Euclidean weights and binary layers, independently of a particular code. -/
namespace Atlas.Codes.Quaternary
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem euclideanSymbolWeight_eq_zero (a : Quat) : euclideanSymbolWeight a=0 ↔ a=0 := by
  decide +kernel +revert

theorem euclideanWeight_eq_zero (w : ι → Quat) : euclideanWeight w=0 ↔ w=0 := by
  classical
  simp [euclideanWeight,Finset.sum_eq_zero_iff,euclideanSymbolWeight_eq_zero,funext_iff]

theorem residue_weight_le (w : ι → Quat) : hammingNorm (reduce w) ≤ euclideanWeight w := by
  classical
  have h (a : Quat) : (if reduceScalar a=0 then 0 else 1 : ℕ) ≤ euclideanSymbolWeight a := by
    decide +kernel +revert
  simp only [hammingNorm,Finset.card_filter,euclideanWeight]
  apply Finset.sum_le_sum
  intro i _
  by_cases hz : reduceScalar (w i)=0
  · simp [reduce,hz]
  · simpa [reduce,hz] using h (w i)

theorem euclideanWeight_double (b : ι → Binary) :
    euclideanWeight (double b)=4*hammingNorm b := by
  classical
  have h (a : Binary) : euclideanSymbolWeight (doubleScalar a)=
      (if a=0 then 0 else 4) := by decide +kernel +revert
  simp only [euclideanWeight,double,AddMonoidHom.coe_mk,ZeroHom.coe_mk,h]
  simp [hammingNorm,Finset.card_filter,Finset.mul_sum,mul_ite]

end Atlas.Codes.Quaternary
