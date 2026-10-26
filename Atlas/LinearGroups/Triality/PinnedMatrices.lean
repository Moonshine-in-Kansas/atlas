import Atlas.LinearGroups.Triality.AbsoluteRoots

/-! Matrix entries and commuting outer nodes for the chosen D4 pinning. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable {K : Type*} [Field K]

/-- Matrix coefficients in the specified positive/negative coordinate basis. -/
def coefficients (g : O_DPlus 4 K) : Matrix (Index 4) (Index 4) K :=
  fun i j => g.val (Pi.single j 1) i

set_option maxHeartbeats 2000000 in
/-- The negative pinned roots are literally the transposes of the positive ones. -/
theorem pinnedNegative_coefficients (r : Fin 4) (t : K) :
    coefficients (pinnedNegativeRoot r t) = (coefficients (pinnedRoot r t)).transpose := by
  ext i j
  fin_cases r <;> cases i with
  | inl i => cases j with
    | inl j => fin_cases i <;> fin_cases j <;>
        simp [coefficients, pinnedRoot, pinnedNegativeRoot, differenceRoot_apply,
          sumRoot_apply, negativeSumRoot_apply, e, f, Pi.single_apply, Matrix.transpose_apply]
    | inr j => fin_cases i <;> fin_cases j <;>
        simp [coefficients, pinnedRoot, pinnedNegativeRoot, differenceRoot_apply,
          sumRoot_apply, negativeSumRoot_apply, e, f, Pi.single_apply, Matrix.transpose_apply]
  | inr i => cases j with
    | inl j => fin_cases i <;> fin_cases j <;>
        simp [coefficients, pinnedRoot, pinnedNegativeRoot, differenceRoot_apply,
          sumRoot_apply, negativeSumRoot_apply, e, f, Pi.single_apply, Matrix.transpose_apply]
    | inr j => fin_cases i <;> fin_cases j <;>
        simp [coefficients, pinnedRoot, pinnedNegativeRoot, differenceRoot_apply,
          sumRoot_apply, negativeSumRoot_apply, e, f, Pi.single_apply, Matrix.transpose_apply]

end Atlas.Triality
