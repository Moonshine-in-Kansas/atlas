import Atlas.Fischer.RootAxisInvariant
import Atlas.Fischer.RootFamilyParameters

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem basicAxis_ray_injective : Function.Injective (fun i => rootRay (basicAxis i)) := by
  intro i j h
  have hv := rootRay_eq_of_axisSum (basicAxis j) (basicAxis i)
    (by rw [rootAxisSum_basic, rootAxisSum_basic]) (by rw [rootAxisSum_basic]; norm_num) h
  by_contra hij
  have he := congrFun hv (.inl i)
  simp only [basicAxis, ite_true, if_neg hij] at he
  norm_num at he

theorem octadic_ray_eq_implies_octad_eq {O P : Octad}
    (Q : OctadCalibration O) (R : OctadCalibration P)
    (χ : OctadicCharacter O) (ψ : OctadicCharacter P)
    (h : rootRay (octadicRoot Q χ) = rootRay (octadicRoot R ψ)) : O = P := by
  classical
  have hv := rootRay_eq_of_axisSum (octadicRoot R ψ) (octadicRoot Q χ)
    (by rw [rootAxisSum_octadic, rootAxisSum_octadic])
    (by rw [rootAxisSum_octadic]; norm_num) h
  apply Subtype.ext
  apply Finset.ext
  intro i
  have he := congrFun hv (.inl i)
  rw [octadicRoot_axis_coefficient, octadicRoot_axis_coefficient] at he
  by_cases hO : i ∈ O.val <;> by_cases hP : i ∈ P.val <;> simp_all <;> norm_num at he

theorem octadicRoot_ray_injective {O : Octad} (Q : OctadCalibration O) :
    Function.Injective (fun χ => rootRay (octadicRoot Q χ)) := by
  intro χ ψ h
  apply octadicRoot_injective Q
  exact rootRay_eq_of_axisSum _ _
    (by rw [rootAxisSum_octadic, rootAxisSum_octadic])
    (by rw [rootAxisSum_octadic]; norm_num) h

theorem octadicParameter_ray_injective : Function.Injective
    (fun t : OctadicRootParameter => rootRay (octadicRoot (chosenOctadCalibration t.1) t.2)) := by
  rintro ⟨O, χ⟩ ⟨P, ψ⟩ h
  have hOP := octadic_ray_eq_implies_octad_eq _ _ _ _ h
  change O = P at hOP
  subst P
  have hχ := octadicRoot_ray_injective (chosenOctadCalibration O) h
  change χ = ψ at hχ
  subst ψ
  rfl

theorem basic_octadic_rays_ne (i : Omega) {O : Octad}
    (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    rootRay (basicAxis i) ≠ rootRay (octadicRoot Q χ) := by
  intro h
  have hc := rootAxisSum_cube_of_ray_eq _ _ h
  rw [rootAxisSum_basic, rootAxisSum_octadic] at hc
  norm_num at hc

end Atlas.Fischer
