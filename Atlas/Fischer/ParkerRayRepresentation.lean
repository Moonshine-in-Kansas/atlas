import Atlas.Fischer.FullSemilinearQuotient

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The retained Parker group acting faithfully on the actual root rays. -/
def parkerRayHom : ParkerStandardGroup →* rootGeneratedRayGroup :=
  fullSemilinearRayProjection.comp parkerAlgebraRepresentation

theorem parkerRayHom_injective : Function.Injective parkerRayHom := by
  intro h k he
  have hk : parkerAlgebraRepresentation (h*k⁻¹) ∈ fullSemilinearRayProjection.ker := by
    change parkerRayHom (h*k⁻¹)=1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  rw [fullSemilinearRayProjection_kernel] at hk
  obtain ⟨a,ha⟩ := hk
  have hpair : (1,h*k⁻¹)=(a,1) := scalar_parker_factor_injective (by
    simpa only [map_one,one_mul,mul_one] using ha.symm)
  have hp := congrArg Prod.snd hpair
  exact mul_inv_eq_one.mp hp

theorem parkerRayHom_basic (h : ParkerStandardGroup) (i : Omega) :
    (parkerRayHom h).val (displayedRayOfParameter (.inl i))=
      displayedRayOfParameter (.inl ((parkerStandardProjection h).val i)) := by
  apply Subtype.ext
  change (semilinearDisplayedRayAction (parkerAlgebraRepresentation h)
    (displayedRayOfParameter (.inl i))).val= _
  rw [semilinearDisplayedRayAction_parameter_value]
  change rootRay (parkerCoordinateAction h (basicAxis i))=_
  rw [parkerCoordinateAction_basicAxis]
  rfl

theorem parkerRayHom_conjugate_basic (h : ParkerStandardGroup) (i : Omega) :
    parkerRayHom h * distinguishedRootElement (.inl i) * (parkerRayHom h)⁻¹=
      distinguishedRootElement (.inl ((parkerStandardProjection h).val i)) :=
  distinguishedRootElement_conjugation _ _ _ (parkerRayHom_basic h i)

theorem parkerRayHom_commutes_basic_iff (h : ParkerStandardGroup) (i : Omega) :
    Commute (parkerRayHom h) (distinguishedRootElement (.inl i)) ↔
      (parkerStandardProjection h).val i=i := by
  constructor
  · intro hc
    have he : parkerRayHom h * distinguishedRootElement (.inl i) * (parkerRayHom h)⁻¹=
        distinguishedRootElement (.inl i) := mul_inv_eq_iff_eq_mul.mpr hc.eq
    rw [parkerRayHom_conjugate_basic] at he
    exact Sum.inl.inj (distinguishedRootElement_injective he)
  · intro hi
    have he := parkerRayHom_conjugate_basic h i
    rw [hi] at he
    exact mul_inv_eq_iff_eq_mul.mp he

end Atlas.Fischer
