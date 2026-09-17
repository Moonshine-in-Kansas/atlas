import Atlas.Fischer.OctadicRootOrbit
import Atlas.Fischer.DuadFibreChoiceIndependence
import Atlas.Fischer.ParkerAlgebraRepresentation

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Phase correction is in the actual cocode kernel, so retains the prescribed
Mathieu coordinate permutation. -/
theorem octadicRoot_parker_transport_with_projection (e : ParkerStandardGroup)
    {O P : Octad} (Q : OctadCalibration O) (R : OctadCalibration P)
    (he : parkerOctadAction e O=P) (χ : OctadicCharacter O) (ψ : OctadicCharacter P) :
    ∃ f : ParkerStandardGroup,parkerStandardProjection f=parkerStandardProjection e ∧
      parkerCoordinateAction f (octadicRoot Q χ)=octadicRoot R ψ := by
  subst P
  let χe := (octadCharacterPullback e O).symm χ
  have hx : parkerCoordinateAction e (octadicRoot Q χ)=
      octadicRoot R (χe+octadCalibrationDifference R (octadCalibrationTransport e Q)) := by
    rw [parkerCoordinateAction_octadicRoot,octadicRoot_change R (octadCalibrationTransport e Q)]
  obtain ⟨d,hd⟩ := octadicRoot_cocode_transitive R
    (χe+octadCalibrationDifference R (octadCalibrationTransport e Q)) ψ
  refine ⟨parkerCocodeStandard d*e,?_,?_⟩
  · rw [map_mul,parkerCocodeStandard_projection,one_mul]
  · rw [parkerCoordinateAction_mul,hx,hd]

/-- Actual Parker transport sends a chosen duadic vector to the chosen fibre
on the transported duad, with its scalar phase fixed by the point coordinates. -/
theorem chosenDuadicRoot_parker_fibre (e : ParkerStandardGroup) (p q : RootDuad)
    (he : permuteBlock (parkerStandardProjection e).val p.val=q.val)
    (ξ : Module.Dual Bit (duadShortenedCode p.val)) :
    ∃ η,parkerCoordinateAction e (chosenDuadicRoot p ξ)=chosenDuadicRoot q η := by
  classical
  apply reflectingRoot_duadic_shape_is_chosen q
  · exact semilinearAlgebra_isReflectingRoot (parkerAlgebraRepresentation e) _
      (reflectingRootParameter_isReflectingRoot (.inr (.inr ⟨p,ξ⟩)))
  · intro j
    obtain ⟨i,rfl⟩ := (parkerStandardProjection e).val.surjective j
    have h := parkerCoordinateAction_at_image e (chosenDuadicRoot p ξ) (.inl i)
    change parkerCoordinateAction e (chosenDuadicRoot p ξ) (.inl ((parkerStandardProjection e).val i))=
      parkerScalarSign 0*scalarParityAut (parkerStandardParity e).toAdd (chosenDuadicRoot p ξ (.inl i)) at h
    rw [h,chosenDuadicRoot_axis_coefficient]
    have hm : (parkerStandardProjection e).val i∈q.val ↔ i∈p.val := by
      rw [← he]
      exact Finset.mem_image.trans ⟨fun ⟨k,hk,hki⟩ =>
        (parkerStandardProjection e).val.injective hki ▸ hk,fun hi => ⟨i,hi,rfl⟩⟩
    simp only [hm]
    split_ifs <;> norm_num [parkerScalarSign,map_div,map_ofNat]

theorem chosenDuadicRoot_parker_transport_with_projection (e : ParkerStandardGroup)
    (p q : RootDuad) (he : permuteBlock (parkerStandardProjection e).val p.val=q.val)
    (ξ : Module.Dual Bit (duadShortenedCode p.val))
    (η : Module.Dual Bit (duadShortenedCode q.val)) :
    ∃ f : ParkerStandardGroup,parkerStandardProjection f=parkerStandardProjection e ∧
      parkerCoordinateAction f (chosenDuadicRoot p ξ)=chosenDuadicRoot q η := by
  obtain ⟨μ,hμ⟩ := chosenDuadicRoot_parker_fibre e p q he ξ
  obtain ⟨d,hd⟩ := duadCharacterProduct_transitive q.val q.prop
    (duadChosenOctadPair q.val q.prop).1 (duadChosenOctadPair q.val q.prop).2
    (duadChosenOctadPair_intersection q.val q.prop)
    (chosenOctadCalibration _) (chosenOctadCalibration _) μ η
  refine ⟨parkerCocodeStandard d*e,?_,?_⟩
  · rw [map_mul,parkerCocodeStandard_projection,one_mul]
  · rw [parkerCoordinateAction_mul,hμ]
    exact hd

end Atlas.Fischer
