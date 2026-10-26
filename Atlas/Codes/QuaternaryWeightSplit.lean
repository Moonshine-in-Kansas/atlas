import Atlas.Codes.QuaternaryWeight
import Atlas.Codes.Weight

/-! Euclidean weight split into odd coordinates and entries equal to two. -/
namespace Atlas.Codes.Quaternary
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

noncomputable def twoCount (w : ι → Quat) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => w i=2)).card

theorem euclideanWeight_split (w : ι → Quat) :
    euclideanWeight w=hammingNorm (reduce w)+4*twoCount w := by
  classical
  have h (a : Quat) : euclideanSymbolWeight a=
      (if reduceScalar a≠0 then 1 else 0 : ℕ)+4*(if a=2 then 1 else 0) := by
    decide +kernel +revert
  rw [Atlas.Codes.hammingNorm_eq_sum]
  simp [ -Finset.sum_boole, euclideanWeight,h,twoCount,Finset.sum_add_distrib,Finset.mul_sum,
    Finset.card_filter,reduce]
  rfl

theorem twoCount_eq_zero (w : ι → Quat) : twoCount w=0 ↔ ∀ i,w i≠2 := by
  classical
  simp [twoCount,Finset.card_eq_zero,Finset.filter_eq_empty_iff]

theorem euclideanWeight_eq_residue_iff (w : ι → Quat) :
    euclideanWeight w=hammingNorm (reduce w) ↔ ∀ i,w i≠2 := by
  rw [euclideanWeight_split,← twoCount_eq_zero]
  omega

end Atlas.Codes.Quaternary
