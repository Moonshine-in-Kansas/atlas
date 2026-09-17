import Atlas.Fischer.BasicOctadicRays
import Atlas.Fischer.DuadicPointRays
import Atlas.Fischer.ReflectingRootAutomorphisms

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The only remaining injection input is the character injection for each
actual chosen duadic product family. Point-shape separation is already proved. -/
theorem duadicParameter_ray_injective
    (hi : ∀ p : RootDuad, Function.Injective (chosenDuadicRoot p)) :
    Function.Injective (fun t : DuadicRootParameter => rootRay (chosenDuadicRoot t.1 t.2)) := by
  rintro ⟨p, ξ⟩ ⟨q, η⟩ h
  have hpq := chosenDuadicRoot_ray_eq_implies_duad_eq p q ξ η h
  subst q
  have hv := rootRay_eq_of_axisSum (chosenDuadicRoot p η) (chosenDuadicRoot p ξ)
    (by rw [chosenDuadicRoot_axisSum, chosenDuadicRoot_axisSum])
    (by rw [chosenDuadicRoot_axisSum]; norm_num) h
  have he := hi p hv
  subst η
  rfl

theorem reflectingRootParameterRay_injective_of_duadic
    (hi : ∀ p : RootDuad, Function.Injective (chosenDuadicRoot p)) :
    Function.Injective reflectingRootParameterRay := by
  intro a b h
  rcases a with i | (a | a) <;> rcases b with j | (b | b)
  · exact congrArg Sum.inl (basicAxis_ray_injective h)
  · exact False.elim (basic_octadic_rays_ne i (chosenOctadCalibration b.1) b.2 h)
  · exact False.elim (basic_chosenDuadic_rays_ne i b.1 b.2 h)
  · exact False.elim (basic_octadic_rays_ne j (chosenOctadCalibration a.1) a.2 h.symm)
  · exact congrArg (fun t : OctadicRootParameter => Sum.inr (Sum.inl t))
      (octadicParameter_ray_injective h)
  · exact False.elim (octadic_chosenDuadic_rays_ne (chosenOctadCalibration a.1) a.2 b.1 b.2 h)
  · exact False.elim (basic_chosenDuadic_rays_ne j a.1 a.2 h.symm)
  · exact False.elim (octadic_chosenDuadic_rays_ne (chosenOctadCalibration b.1) b.2 a.1 a.2 h.symm)
  · exact congrArg (fun t : DuadicRootParameter => Sum.inr (Sum.inr t))
      (duadicParameter_ray_injective hi h)

/-- The actual image of the explicitly constructed roots under normalized rays. -/
def DisplayedReflectingRay := Set.range reflectingRootParameterRay

theorem displayedReflectingRay_card_of_duadic
    (hi : ∀ p : RootDuad, Function.Injective (chosenDuadicRoot p)) :
    Nat.card DisplayedReflectingRay = 306936 := by
  rw [DisplayedReflectingRay, ← Nat.card_congr
    (Equiv.ofInjective reflectingRootParameterRay (reflectingRootParameterRay_injective_of_duadic hi))]
  exact reflectingRootParameter_card

theorem reflectingRootParameter_exhaust_of_duadic
    (hi : ∀ p : RootDuad, Function.Injective (chosenDuadicRoot p))
    (x : Coordinates) (hx : IsReflectingRoot x) :
    ∃ t : ReflectingRootParameter, rootRay x = reflectingRootParameterRay t := by
  letI : Fintype ReflectingRootParameter := Fintype.ofFinite _
  exact extremalReflectingRays_exhaust reflectingRootParameterVector
    reflectingRootParameter_isReflectingRoot (reflectingRootParameterRay_injective_of_duadic hi)
    (by rw [← Nat.card_eq_fintype_card]; exact reflectingRootParameter_card) x hx

theorem reflectingRootParameter_membership_of_duadic
    (hi : ∀ p : RootDuad, Function.Injective (chosenDuadicRoot p)) (x : Coordinates) :
    IsReflectingRoot x ↔ ∃ t : ReflectingRootParameter, x ∈ reflectingRootParameterRay t := by
  letI : Fintype ReflectingRootParameter := Fintype.ofFinite _
  exact extremalReflectingRays_membership reflectingRootParameterVector
    reflectingRootParameter_isReflectingRoot (reflectingRootParameterRay_injective_of_duadic hi)
    (by rw [← Nat.card_eq_fintype_card]; exact reflectingRootParameter_card) x

theorem reflectingRootParameter_automorphism_of_duadic
    (hi : ∀ p : RootDuad, Function.Injective (chosenDuadicRoot p))
    (e : SemilinearAlgebraAutomorphism) (t : ReflectingRootParameter) :
    ∃ s, rootRay (e.val (reflectingRootParameterVector t)) = reflectingRootParameterRay s :=
  reflectingRootParameter_exhaust_of_duadic hi _
    (semilinearAlgebra_isReflectingRoot e _ (reflectingRootParameter_isReflectingRoot t))

end Atlas.Fischer
