import Atlas.LinearGroups.ReeG2.ProjectiveAction

noncomputable section
namespace Atlas.ReeG2
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- Only the two distinguished points are handled here; this is not full Weyl preservation. -/
theorem pointRight_zero_upsilon (m : ℕ) :
    pointRight (upsilon : Ambient F) (affinePoint m 0 0 0) = infinityPoint := by
  unfold pointRight affinePoint infinityPoint
  rw [Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨-1,?_⟩
  ext i
  fin_cases i <;>
    simp [rowEquiv_apply, affineVector, rootMatrix_zero, infinityVector,
      upsilon, upsilonMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Units.smul_def]

theorem pointRight_infinity_upsilon (m : ℕ) :
    pointRight (upsilon : Ambient F) infinityPoint = affinePoint m 0 0 0 := by
  have h := congrArg (pointRight (upsilon : Ambient F)) (pointRight_zero_upsilon (F := F) m)
  have hi : pointRight (upsilon : Ambient F) ∘ pointRight upsilon = id := by
    rw [← pointRight_mul,upsilon_square,pointRight_one]
  have hv := congrFun hi (affinePoint (F := F) m 0 0 0)
  exact h.symm.trans hv
end Atlas.ReeG2
