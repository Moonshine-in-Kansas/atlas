import Atlas.Fischer.RootFamilyParameters
import Atlas.Fischer.DuadicRayShape
import Atlas.Fischer.DuadProductPointCoordinates

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem chosenDuadicRoot_axis_coefficient (p : RootDuad)
    (ξ : Module.Dual Bit (duadShortenedCode p.val)) (i : Omega) :
    chosenDuadicRoot p ξ (.inl i) = if i ∈ p.val then (-7 / 8 : Scalar) else 1 / 8 := by
  unfold chosenDuadicRoot duadCharacterProduct
  rw [duadOctadicProduct_axis_coefficient
    (by rw [duadChosenOctadPair_intersection]; exact p.property)]
  rw [duadChosenOctadPair_intersection]

theorem chosenDuadicRoot_axisSum (p : RootDuad)
    (ξ : Module.Dual Bit (duadShortenedCode p.val)) : rootAxisSum (chosenDuadicRoot p ξ) = 1 :=
  rootAxisSum_duadic_shape p.val p.property _ (chosenDuadicRoot_axis_coefficient p ξ)

theorem chosenDuadicRoot_ray_eq_implies_duad_eq (p q : RootDuad)
    (ξ : Module.Dual Bit (duadShortenedCode p.val))
    (η : Module.Dual Bit (duadShortenedCode q.val))
    (h : rootRay (chosenDuadicRoot p ξ) = rootRay (chosenDuadicRoot q η)) : p = q :=
  Subtype.ext (duadic_shape_ray_implies_duad_eq p.val q.val p.property q.property _ _
    (chosenDuadicRoot_axis_coefficient p ξ) (chosenDuadicRoot_axis_coefficient q η) h)

theorem basic_chosenDuadic_rays_ne (i : Omega) (p : RootDuad)
    (ξ : Module.Dual Bit (duadShortenedCode p.val)) :
    rootRay (basicAxis i) ≠ rootRay (chosenDuadicRoot p ξ) :=
  basic_duadic_shape_rays_ne i p.val p.property _ (chosenDuadicRoot_axis_coefficient p ξ)

theorem octadic_chosenDuadic_rays_ne {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (p : RootDuad) (ξ : Module.Dual Bit (duadShortenedCode p.val)) :
    rootRay (octadicRoot Q χ) ≠ rootRay (chosenDuadicRoot p ξ) :=
  octadic_duadic_shape_rays_ne Q χ p.val p.property _ (chosenDuadicRoot_axis_coefficient p ξ)

end Atlas.Fischer
