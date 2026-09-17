import Atlas.Conway.IcosianAxisTransitionEvaluation
import Atlas.Conway.IcosianLocalBReference
import Atlas.Conway.IcosianRootLocalReferences
import Atlas.Lattices.IcosianRootPermutations

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

def icosianAxisLinkBInput : IcosianRoot :=
  icosianRootPermute (Equiv.swap 0 1) icosianLocalBRoot

def icosianAxisLinkCInput : IcosianRoot :=
  icosianRootPermute (Equiv.swap 0 1) icosianLocalCRoot

/-- An axis-fixing reflection word joins the nonorthogonal B and C local pieces. -/
theorem icosianAxisTransition_B_C_norm (j : Fin 3) :
    icosianNorm ((icosianAxisTransitionWord 0).val
      (icosianCoordinateEmbedding icosianAxisLinkBInput.val) j)=(![2,1,1] j) := by
  rw [icosianAxisTransitionWord_matrix_apply]
  fin_cases j <;> decide +kernel

/-- A second axis-fixing word joins the norm-one C and D local pieces. -/
theorem icosianAxisTransition_C_D_norm (j : Fin 3) :
    icosianNorm ((icosianAxisTransitionWord 1).val
      (icosianCoordinateEmbedding icosianAxisLinkCInput.val) j)=
        (![1,1+goldenTau,2-goldenTau] j) := by
  rw [icosianAxisTransitionWord_matrix_apply]
  fin_cases j <;> decide +kernel

end Atlas.Conway
