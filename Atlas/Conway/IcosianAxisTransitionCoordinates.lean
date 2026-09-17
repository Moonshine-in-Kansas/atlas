import Atlas.Conway.IcosianAxisTransitionIntermediateData

set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianAxisTransitionTarget_embedding : ∀ k i,
    icosianCoordinateEmbedding (icosianAxisTransitionTarget k i).val=
      icosianAxisTransitionTargetRaw k i := by
  intro k i
  funext j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    apply QuaternionAlgebra.ext <;> decide +kernel

/-- The first reflection is evaluated once on each coordinate root vector. -/
theorem icosianAxisFirst_step : ∀ i,
    icosianReflection (icosianAxisTransitionRoot 0) (Pi.single i 2)=
      icosianAxisFirstVector i := by
  intro i
  funext j
  fin_cases i <;> fin_cases j <;> apply QuaternionAlgebra.ext <;> decide +kernel

/-- The middle reflected vectors are checked separately, avoiding nested reduction. -/
theorem icosianAxisMiddle_step : ∀ (k i : Fin 3),
    icosianReflection (icosianAxisTransitionRoot ⟨k.val+1,by omega⟩)
      (fun j => if j=1 then -icosianAxisFirstVector i j else icosianAxisFirstVector i j)=
      icosianAxisMiddleVector k i := by
  intro k i
  funext j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    apply QuaternionAlgebra.ext <;> decide +kernel

/-- Each last step involves just one reflection in the displayed local root. -/
theorem icosianAxisLast_step : ∀ (k i : Fin 3),
    icosianReflection (icosianAxisTransitionRoot 0) (icosianAxisMiddleVector k i)=
      icosianRightMul (icosianAxisTransitionTargetRaw ⟨k.val,by omega⟩ i)
        (icosianAxisTransitionScalar ⟨k.val,by omega⟩ i) := by
  intro k i
  funext j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    apply QuaternionAlgebra.ext <;> decide +kernel

theorem icosianAxisTransitionBaseRaw_axes (k i : Fin 3) :
    icosianAxisTransitionBaseRaw k (Pi.single i 2)=
      icosianRightMul (icosianAxisTransitionTargetRaw ⟨k.val,by omega⟩ i)
        (icosianAxisTransitionScalar ⟨k.val,by omega⟩ i) := by
  unfold icosianAxisTransitionBaseRaw
  rw [icosianAxisFirst_step,icosianAxisMiddle_step]
  exact icosianAxisLast_step k i

theorem icosianAxisTransitionFinalEdge_axes : ∀ i j,
    icosianReflectionEdgeDiagonalRaw 1 0
      (icosianRightMul (icosianAxisTransitionTargetRaw 0 i) (icosianAxisTransitionScalar 0 i)) j=
      icosianAxisTransitionTargetRaw 3 i j * icosianAxisTransitionScalar 3 i := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply QuaternionAlgebra.ext <;> decide +kernel

/-- Twelve local images assembled from separately checked single-reflection steps. -/
theorem icosianAxisTransitionRaw_axes : ∀ k i j,
    icosianAxisTransitionRaw k (Pi.single i 2) j=
      icosianAxisTransitionTargetRaw k i j * icosianAxisTransitionScalar k i := by
  intro k i j
  fin_cases k
  · exact congrFun (icosianAxisTransitionBaseRaw_axes 0 i) j
  · exact congrFun (icosianAxisTransitionBaseRaw_axes 1 i) j
  · exact congrFun (icosianAxisTransitionBaseRaw_axes 2 i) j
  · change icosianReflectionEdgeDiagonalRaw 1 0
      (icosianAxisTransitionBaseRaw 0 (Pi.single i 2)) j=_
    rw [icosianAxisTransitionBaseRaw_axes]
    exact icosianAxisTransitionFinalEdge_axes i j

end Atlas.Conway
