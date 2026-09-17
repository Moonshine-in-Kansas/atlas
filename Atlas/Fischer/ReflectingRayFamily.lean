import Atlas.Fischer.RootFamilyRayAssembly
import Atlas.Fischer.DuadProductInjectivity

noncomputable section
namespace Atlas.Fischer

/-- Actual character injection, specialized only to the retained chosen pair. -/
theorem chosenDuadicRoot_injective (p : RootDuad) : Function.Injective (chosenDuadicRoot p) :=
  duadCharacterProduct_injective p.val p.property
    (duadChosenOctadPair p.val p.property).1 (duadChosenOctadPair p.val p.property).2
    (duadChosenOctadPair_intersection p.val p.property)
    (chosenOctadCalibration _) (chosenOctadCalibration _)

theorem reflectingRootParameterRay_injective : Function.Injective reflectingRootParameterRay :=
  reflectingRootParameterRay_injective_of_duadic chosenDuadicRoot_injective

/-- Exact cardinality of the actual constructed ray image, after full injection. -/
theorem displayedReflectingRay_card : Nat.card DisplayedReflectingRay = 306936 :=
  displayedReflectingRay_card_of_duadic chosenDuadicRoot_injective

/-- Intrinsic reflecting roots are exhausted by the actual constructed family. -/
theorem reflectingRootParameter_exhaust (x : Coordinates) (hx : IsReflectingRoot x) :
    ∃ t : ReflectingRootParameter, rootRay x = reflectingRootParameterRay t :=
  reflectingRootParameter_exhaust_of_duadic chosenDuadicRoot_injective x hx

theorem reflectingRootParameter_membership (x : Coordinates) :
    IsReflectingRoot x ↔ ∃ t : ReflectingRootParameter, x ∈ reflectingRootParameterRay t :=
  reflectingRootParameter_membership_of_duadic chosenDuadicRoot_injective x

theorem reflectingRootParameter_automorphism (e : SemilinearAlgebraAutomorphism)
    (t : ReflectingRootParameter) :
    ∃ s, rootRay (e.val (reflectingRootParameterVector t)) = reflectingRootParameterRay s :=
  reflectingRootParameter_automorphism_of_duadic chosenDuadicRoot_injective e t

end Atlas.Fischer
