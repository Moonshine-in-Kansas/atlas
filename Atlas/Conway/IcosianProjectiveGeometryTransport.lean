import Atlas.Conway.IcosianProjectiveModel
import Mathlib.GroupTheory.GroupAction.Primitive

noncomputable section
namespace Atlas.Conway
open MulAction

theorem icosianProjectiveProjection_surjective :
    Function.Surjective icosianProjectiveProjection := QuotientGroup.mk'_surjective _

/-- Full point-stabilizer orbits are unchanged by passing to the actual sign
quotient. Every quotient stabilizer element lifts to the full linear stabilizer. -/
theorem icosianProjectiveStabilizer_orbit (p q : IcosianRootPoint) :
    orbit (stabilizer IcosianProjectiveModel p) q=
      orbit (stabilizer icosianHermitianGroup p) q := by
  ext r
  constructor
  · rintro ⟨g,rfl⟩
    obtain ⟨c,hc⟩ := icosianProjectiveProjection_surjective g.val
    have hn : c∈stabilizer icosianHermitianGroup p := by
      change c • p=p
      rw [← icosianProjectivePointAction_mk,hc]
      exact g.property
    refine ⟨⟨c,hn⟩,?_⟩
    change c • q=g.val • q
    rw [← icosianProjectivePointAction_mk,hc]
  · rintro ⟨g,rfl⟩
    have hn : icosianProjectiveProjection g.val∈stabilizer IcosianProjectiveModel p := by
      change icosianProjectiveProjection g.val • p=p
      rw [icosianProjectivePointAction_mk]
      exact g.property
    refine ⟨⟨icosianProjectiveProjection g.val,hn⟩,?_⟩
    exact icosianProjectivePointAction_mk g.val q

theorem icosianProjective_primitive_of_linear
    [IsPreprimitive icosianHermitianGroup IcosianRootPoint] :
    IsPreprimitive IcosianProjectiveModel IcosianRootPoint := by
  let f : IcosianRootPoint →ₑ[icosianProjectiveProjection] IcosianRootPoint :=
    ⟨id,fun g p => (icosianProjectivePointAction_mk g p).symm⟩
  exact IsPreprimitive.of_surjective (f := f) Function.surjective_id

end Atlas.Conway
