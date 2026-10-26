import Atlas.LinearGroups.Orthogonal.Minus.SingularConnectors
import Atlas.LinearGroups.Orthogonal.NonperpendicularOrbit
import Atlas.LinearGroups.Orthogonal.SingularProjectiveAction
import Atlas.GroupTheory.RankThreePrimitive

/-! # Faithful primitive singular-line action for actual projective minus group

All characteristics are included. The two stabilizer orbits and their geometric
connectors prove primitivity directly; no order or simplicity result is used.
-/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem singularPoints_pretransitive_minus (hdeg : Module.finrank F K = 2) (n : ℕ) :
    MulAction.IsPretransitive (elementarySubgroup (form hdeg (n+2)))
      (SingularPoints (form hdeg (n+2))) :=
  singularPoints_pretransitive _ (elementary_singular_transport hdeg n)

theorem singularPoints_primitive (hdeg : Module.finrank F K = 2) (n : ℕ) :
    MulAction.IsPreprimitive (elementarySubgroup (form hdeg (n+3)))
      (SingularPoints (form hdeg (n+3))) := by
  letI := singularPoints_pretransitive_minus hdeg (n+1)
  let Q := form hdeg (n+3)
  let H := wittTwoFrame hdeg (F := F) (n+1)
  let a := singularPointMk Q H.e₁ (Atlas.Quadratic.WittTwoFrame.first_ne_zero Q H) H.qe₁
  apply Atlas.GroupTheory.primitive_of_two_suborbits_and_connectors a
    (SingularPerp Q) (singularPerp_symmetric Q)
    (singular_stabilizer_perpendicular_transitive hdeg n)
    (singular_stabilizer_nonperpendicular_transitive Q)
  · intro p r _ hpr
    exact singularPoints_perpendicular_connector hdeg (n+1) p r hpr
  · intro p r hpr _
    exact singularPoints_nonperpendicular_connector hdeg (n+1) p r hpr

theorem projectiveSingular_faithful_minus (hdeg : Module.finrank F K = 2) (n : ℕ) :
    FaithfulSMul (ProjectiveElementary (form hdeg (n+2))) (SingularPoints (form hdeg (n+2))) :=
  projectiveSingular_faithful _ (wittTwoFrame hdeg n)

theorem projectiveSingular_primitive (hdeg : Module.finrank F K = 2) (n : ℕ) :
    MulAction.IsPreprimitive (ProjectiveElementary (form hdeg (n+3)))
      (SingularPoints (form hdeg (n+3))) := by
  letI := singularPoints_primitive hdeg n
  let f : SingularPoints (form hdeg (n+3)) →ₑ[projectiveElementaryMap (form hdeg (n+3))]
      SingularPoints (form hdeg (n+3)) :=
    { toFun := id, map_smul' := fun _ _ => rfl }
  exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id

end Atlas.Orthogonal.Minus
