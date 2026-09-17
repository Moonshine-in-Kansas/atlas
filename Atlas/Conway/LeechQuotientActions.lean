import Atlas.Conway.LeechCrossKernel

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

def quotientCrossRepresentation : LeechCentralQuotient →* Equiv.Perm LeechCross :=
  QuotientGroup.lift leechCentralSigns crossRepresentation (le_of_eq crossRepresentation_kernel.symm)

theorem quotientCrossRepresentation_injective : Function.Injective quotientCrossRepresentation :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr crossRepresentation_kernel.symm

theorem quotientCrossRepresentation_compatible (g : LeechIsometryGroup) :
    quotientCrossRepresentation (leechCentralProjection g) = crossRepresentation g := rfl

def quotientModTwoRepresentation :
    LeechCentralQuotient →* (LeechModTwo ≃ₗ[Bit] LeechModTwo) :=
  QuotientGroup.lift leechCentralSigns leechModTwoRepresentation
    (le_of_eq leechModTwoRepresentation_kernel.symm)

theorem quotientModTwoRepresentation_injective : Function.Injective quotientModTwoRepresentation :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr leechModTwoRepresentation_kernel.symm

theorem quotientModTwoRepresentation_compatible (g : LeechIsometryGroup) :
    quotientModTwoRepresentation (leechCentralProjection g) = leechModTwoRepresentation g := rfl

theorem quotientModTwoRepresentation_quadratic (g : LeechCentralQuotient) (a : LeechModTwo) :
    leechQuadratic (quotientModTwoRepresentation g a) = leechQuadratic a := by
  obtain ⟨h,rfl⟩ := leechCentralProjection_surjective g
  exact leechModTwoRepresentation_quadratic h a

theorem quotientCross_modTwo_equivariant (g : LeechCentralQuotient) (X : LeechCross) :
    (quotientCrossRepresentation g X).val = quotientModTwoRepresentation g X.val := by
  obtain ⟨h,rfl⟩ := leechCentralProjection_surjective g
  rfl

end Atlas.Conway
