import Atlas.LinearGroups.Orthogonal.SingularPrimitiveDConnectors
import Atlas.LinearGroups.Orthogonal.NonperpendicularOrbit
import Atlas.LinearGroups.Orthogonal.SingularProjectiveAction
import Atlas.GroupTheory.RankThreePrimitive

/-! # Faithful primitive singular-line action for actual projective split D

All characteristics are included. The two stabilizer orbits and their geometric
connectors prove primitivity directly; no order or simplicity result is used.
-/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F]

theorem singularPointsD_pretransitive (n : ℕ) :
    MulAction.IsPretransitive (elementarySubgroup (formD (n+2) F))
      (SingularPoints (formD (n+2) F)) :=
  singularPoints_pretransitive _ (elementaryD_singular_transport_all_char n)

theorem singularPointsD_primitive (n : ℕ) :
    MulAction.IsPreprimitive (elementarySubgroup (formD (n+3) F))
      (SingularPoints (formD (n+3) F)) := by
  letI := singularPointsD_pretransitive (F := F) (n+1)
  let Q := formD (n+3) F
  let H := wittTwoFrameD (F := F) (n+1)
  let a := singularPointMk Q H.e₁ (Atlas.Quadratic.WittTwoFrame.first_ne_zero Q H) H.qe₁
  apply Atlas.GroupTheory.primitive_of_two_suborbits_and_connectors a
    (SingularPerp Q) (singularPerp_symmetric Q)
    (singular_stabilizerD_perpendicular_transitive n)
    (singular_stabilizer_nonperpendicular_transitive Q)
  · intro p r _ hpr
    exact singularPointsD_perpendicular_connector (n+1) p r hpr
  · intro p r hpr _
    exact singularPointsD_nonperpendicular_connector (n+1) p r hpr

theorem projectiveSingularD_faithful (n : ℕ) :
    FaithfulSMul (ProjectiveElementary (formD (n+2) F)) (SingularPoints (formD (n+2) F)) :=
  projectiveSingular_faithful _ (wittTwoFrameD n)

theorem projectiveSingularD_primitive (n : ℕ) :
    MulAction.IsPreprimitive (ProjectiveElementary (formD (n+3) F))
      (SingularPoints (formD (n+3) F)) := by
  letI := singularPointsD_primitive (F := F) n
  let f : SingularPoints (formD (n+3) F) →ₑ[projectiveElementaryMap (formD (n+3) F)]
      SingularPoints (formD (n+3) F) :=
    { toFun := id, map_smul' := fun _ _ => rfl }
  exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id

end Atlas.Orthogonal
