import Atlas.Fischer.DuadCocodeCoordinateSpan
import Atlas.Fischer.BasicFramePointwiseKernel
import Atlas.Fischer.DuadFibreCount

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem chosenDuadicRoot_cocode (p : RootDuad) (d : Cocode)
    (ξ : Module.Dual Bit (duadShortenedCode p.val)) :
    parkerCoordinateAction (parkerCocodeStandard d) (chosenDuadicRoot p ξ)=
      chosenDuadicRoot p (duadCocodeCharacterAction p.val d ξ) :=
  duadCharacterProduct_cocode _ _ _ _ _ _ _ _ _

theorem chosenDuadicRoot_cocode_stabilizer (p : RootDuad) (d : Cocode)
    (ξ : Module.Dual Bit (duadShortenedCode p.val)) :
    parkerCoordinateAction (parkerCocodeStandard d) (chosenDuadicRoot p ξ)=chosenDuadicRoot p ξ ↔
      d ∈ coordinateCocodeSpan p.val := by
  rw [← duadCocodeAnnihilator_eq_coordinateSpan p.val p.prop]
  exact duadProductFibre_cocode_stabilizer _ _ _ _ _ _ _ _ _

/-- The exact cocode stabilizer of each actual duadic ray is its two-coordinate
span. No scalar ambiguity remains, since the characters give distinct rays. -/
theorem generatedCocodeRayHom_duadic_stabilizer (p : RootDuad) (d : Multiplicative Cocode)
    (ξ : Module.Dual Bit (duadShortenedCode p.val)) :
    (generatedCocodeRayHom d).val (displayedRayOfParameter (.inr (.inr ⟨p,ξ⟩)))=
      displayedRayOfParameter (.inr (.inr ⟨p,ξ⟩)) ↔ d.toAdd ∈ coordinateCocodeSpan p.val := by
  rw [← chosenDuadicRoot_cocode_stabilizer p d.toAdd ξ]
  constructor
  · intro h
    have hr := congrArg Subtype.val h
    change (semilinearDisplayedRayAction (cocodeAlgebraHom d)
      (displayedRayOfParameter (.inr (.inr ⟨p,ξ⟩)))).val=_ at hr
    rw [semilinearDisplayedRayAction_parameter_value] at hr
    change rootRay ((cocodeAlgebraHom d).val (chosenDuadicRoot p ξ))=
      rootRay (chosenDuadicRoot p ξ) at hr
    change rootRay (parkerCoordinateAction (parkerCocodeStandard d.toAdd) (chosenDuadicRoot p ξ))=_ at hr
    rw [chosenDuadicRoot_cocode] at hr
    have ht : (Sum.inr (Sum.inr ⟨p,duadCocodeCharacterAction p.val d.toAdd ξ⟩) : ReflectingRootParameter)=
        .inr (.inr ⟨p,ξ⟩) := reflectingRootParameterRay_injective hr
    have he : duadCocodeCharacterAction p.val d.toAdd ξ=ξ :=
      eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj (Sum.inr.inj ht))).2
    rw [chosenDuadicRoot_cocode,he]
  · intro h
    apply Subtype.ext
    change (semilinearDisplayedRayAction (cocodeAlgebraHom d)
      (displayedRayOfParameter (.inr (.inr ⟨p,ξ⟩)))).val=_
    rw [semilinearDisplayedRayAction_parameter_value]
    change rootRay (parkerCoordinateAction (parkerCocodeStandard d.toAdd) (chosenDuadicRoot p ξ))=_
    rw [h]
    rfl

end Atlas.Fischer
