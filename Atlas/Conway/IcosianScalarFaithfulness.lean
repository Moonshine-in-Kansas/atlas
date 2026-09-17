import Atlas.Conway.IcosianScalarIsometries
import Atlas.Algebra.IcosianNormOneCard

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianScalarRepresentation_injective :
    Function.Injective icosianScalarRepresentation := by
  intro u v h
  have he := congrArg (fun f : IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates =>
    f (fun _ => 1) 0) h
  have hu : (Unitary.toUnits u.val)⁻¹=(Unitary.toUnits v.val)⁻¹ := by
    apply Units.ext
    simpa [icosianScalarRepresentation,icosianRightUnitEquiv,icosianRightMul] using he
  apply Subtype.ext
  exact Unitary.toUnits_injective (inv_inj.mp hu)

theorem icosianScalarsToCo0_injective : Function.Injective icosianScalarsToCo0 := by
  intro u v h
  apply icosianScalarRepresentation_injective
  apply icosianAutomorphismComparison.injective
  have he := congrArg (fun g : LeechIsometryGroup => (fullIsometryEquiv g).val) h
  rw [icosianScalarsToCo0_extension,icosianScalarsToCo0_extension] at he
  exact he

theorem icosianScalarsToCo0_range_card : Nat.card icosianScalarsToCo0.range=120 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective icosianScalarsToCo0_injective).toEquiv]
  exact icosianNormOneGroup_card

end Atlas.Conway
