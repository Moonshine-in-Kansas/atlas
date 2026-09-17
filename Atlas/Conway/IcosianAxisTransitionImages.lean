import Atlas.Conway.IcosianAxisTransitionCoordinates
import Atlas.Conway.IcosianFiveAxisFrames
import Atlas.Conway.IcosianRootFrameAction

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Combinatorics
open scoped Pointwise
attribute [local instance] Classical.propDecidable

theorem icosianRootAxis_embedding (i : Fin 3) :
    icosianCoordinateEmbedding (icosianAxisRoot (i,1)).val=Pi.single i 2 := by
  funext j
  by_cases hj : j=i <;>
    simp [icosianCoordinateEmbedding,icosianAxisRoot,icosianSingle,icosianUnitIntegral,hj] <;> rfl

/-- A scalar-multiple criterion for images of actual root points. -/
theorem icosianRootToPoint_smul_eq_of_rightMul (g : icosianHermitianGroup)
    (r s : IcosianRoot) (a : IcosianQuaternion)
    (he : g.val (icosianCoordinateEmbedding r.val)=
      icosianRightMul (icosianCoordinateEmbedding s.val) a) :
    g • icosianRootToPoint r=icosianRootToPoint s := by
  rw [← icosianRootToPoint_smul]
  apply Subtype.ext
  apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
  refine ⟨MulOpposite.op a,?_⟩
  change icosianRightMul (icosianCoordinateEmbedding s.val) a=
    icosianCoordinateEmbedding (icosianHermitianRoot g r).val
  rw [icosianHermitianRoot_embedding,he]

theorem icosianAxisTransitionWord_axis (k : Fin 4) (i : Fin 3) :
    icosianAxisTransitionWord k • icosianRootAxisPoint i=
      icosianRootToPoint (icosianAxisTransitionTarget k i) := by
  apply icosianRootToPoint_smul_eq_of_rightMul _ _ _ (icosianAxisTransitionScalar k i)
  rw [icosianRootAxis_embedding,icosianAxisTransitionWord_apply,
    icosianAxisTransitionTarget_embedding]
  funext j
  exact icosianAxisTransitionRaw_axes k i j

theorem icosianAxisTransitionWord_fixes_axis (k : Fin 4) :
    icosianAxisTransitionWord k • icosianRootAxisPoint 0=icosianRootAxisPoint 0 := by
  rw [icosianAxisTransitionWord_axis]
  rfl

def icosianAxisTransitionFrameIndex : Fin 4 → Fin 4 := ![1,2,3,0]

attribute [local irreducible] icosianAxisTransitionWord icosianRootToPoint
  icosianEightNeighborRoot icosianAxisRoot

private theorem localEdge_val (j : Fin 4) :
    (icosianLocalEdgeRootFrame j).val=
      {icosianRootAxisPoint 0,
       icosianRootToPoint (icosianEightNeighborRoot (icosianFirstFourIndex j)),
       icosianRootToPoint (icosianEightNeighborRoot
         (icosianEightPartnerIndex (icosianFirstFourIndex j)))} := rfl

/-- Four short words give the four noncoordinate frames through the first axis. -/
theorem icosianAxisTransitionWord_frame (k : Fin 4) :
    icosianAxisTransitionWord k • icosianLocalCoordinateRootFrame=
      icosianLocalEdgeRootFrame (icosianAxisTransitionFrameIndex k) := by
  classical
  apply icosianRootFrame_smul_eq_of_val
  change icosianAxisTransitionWord k •
    ({icosianRootAxisPoint 0,icosianRootAxisPoint 1,icosianRootAxisPoint 2} : Finset IcosianRootPoint)=_
  simp only [Finset.smul_finset_insert,Finset.smul_finset_singleton,icosianAxisTransitionWord_axis]
  rw [localEdge_val]
  fin_cases k
  · rfl
  · rfl
  · rfl
  · change ({icosianRootAxisPoint 0,
        icosianRootToPoint (icosianEightNeighborRoot 7),
        icosianRootToPoint (icosianEightNeighborRoot 0)} : Finset IcosianRootPoint)=
      {icosianRootAxisPoint 0,icosianRootToPoint (icosianEightNeighborRoot 0),
        icosianRootToPoint (icosianEightNeighborRoot 7)}
    rw [Finset.pair_comm (icosianRootToPoint (icosianEightNeighborRoot 7))
      (icosianRootToPoint (icosianEightNeighborRoot 0))]

/-- Every actual frame through the first axis is reached by an axis-fixing
reflection-group element, using the independently proved five-frame exhaustion. -/
theorem icosianReflectionGroup_transitive_axis_frames (F : IcosianRootFrame)
    (hF : icosianRootAxisPoint 0∈F.val) :
    ∃ g : icosianReflectionGroup,
      g.val • icosianRootAxisPoint 0=icosianRootAxisPoint 0 ∧
      g.val • icosianLocalCoordinateRootFrame=F := by
  obtain ⟨i,rfl⟩ := icosianFiveAxisFrames_exhaust F hF
  cases i with
  | inl u =>
    refine ⟨1,?_,?_⟩
    · exact one_smul _ _
    · exact one_smul _ _
  | inr j =>
    have hc : ∃ k,icosianAxisTransitionFrameIndex k=j := by
      fin_cases j
      · exact ⟨3,rfl⟩
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
    obtain ⟨k,hk⟩ := hc
    refine ⟨⟨icosianAxisTransitionWord k,icosianAxisTransitionWord_mem k⟩,
      icosianAxisTransitionWord_fixes_axis k,?_⟩
    change icosianAxisTransitionWord k • icosianLocalCoordinateRootFrame=
      icosianLocalEdgeRootFrame j
    rw [icosianAxisTransitionWord_frame,hk]

end Atlas.Conway
