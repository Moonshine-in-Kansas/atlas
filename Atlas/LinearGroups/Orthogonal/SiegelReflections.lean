import Atlas.LinearAlgebra.QuadraticAnisotropicPerpendicular
import Atlas.LinearGroups.Orthogonal.DicksonSiegel
import Atlas.LinearAlgebra.QuadraticDicksonMultiplicative

/-! # Siegel generators lie in the reflection subgroup in dimension at least five

This uniform proof includes characteristic two and does not assume full-group
reflection generation. A singular parameter splits into two anisotropic parameters.
-/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)
  (hd : 5 ≤ Module.finrank F V)

include hQ hd in
theorem isotropic_parameter_anisotropic_sum_stable (u v : V) (hv : Q v = 0)
    (huv : Q.polarBilin u v = 0) :
    ∃ w₁ w₂, v = w₁+w₂ ∧ Q w₁ ≠ 0 ∧ Q w₂ ≠ 0 ∧
      Q.polarBilin u w₁ = 0 ∧ Q.polarBilin u w₂ = 0 := by
  obtain ⟨w, hw, huw, hvw⟩ := exists_anisotropic_perpendicular_pair Q hQ hd u v
  refine ⟨w, v-w, by abel, hw, ?_, huw, ?_⟩
  · have he : Q (v-w) = Q w := by
      rw [sub_value, hv, hvw]
      ring
    rwa [he]
  · rw [map_sub, huv, huw, sub_zero]

omit [FiniteDimensional F V] in
theorem anisotropic_siegel_mem_reflections (u v : V) (hu : Q u = 0)
    (huv : Q.polarBilin u v = 0) (hv : Q v ≠ 0) :
    siegelElement Q u v hu huv ∈ reflectionSubgroup Q := by
  rw [siegelElement_reflection_factor Q u v hu huv hv]
  exact (reflectionSubgroup Q).mul_mem (reflectionElement_mem _ _ _)
    (reflectionElement_mem _ _ _)

include hQ hd in
theorem siegel_mem_reflections_stable (u v : V) (hu : Q u = 0)
    (huv : Q.polarBilin u v = 0) :
    siegelElement Q u v hu huv ∈ reflectionSubgroup Q := by
  by_cases hv : Q v = 0
  · obtain ⟨w₁, w₂, he, h₁, h₂, hu₁, hu₂⟩ :=
      isotropic_parameter_anisotropic_sum_stable Q hQ hd u v hv huv
    have hs : siegelElement Q u v hu huv =
        siegelElement Q u w₁ hu hu₁ * siegelElement Q u w₂ hu hu₂ := by
      rw [siegelElement_add]
      simpa only [he]
    rw [hs]
    exact (reflectionSubgroup Q).mul_mem
      (anisotropic_siegel_mem_reflections Q u w₁ hu hu₁ h₁)
      (anisotropic_siegel_mem_reflections Q u w₂ hu hu₂ h₂)
  · exact anisotropic_siegel_mem_reflections Q u v hu huv hv

include hQ hd in
theorem elementary_le_reflections_stable : elementarySubgroup Q ≤ reflectionSubgroup Q := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, v, hu, huv, rfl⟩
  exact siegel_mem_reflections_stable Q hQ hd u v hu huv

include hQ hd in
/-- The entire actual elementary subgroup has zero intrinsic parity, before any
identification of the full orthogonal group with its reflection subgroup. -/
theorem dicksonValue_elementary_stable (g : isometrySubgroup Q)
    (hg : g ∈ elementarySubgroup Q) : dicksonValue Q g = 0 := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨u, v, hu, huv, rfl⟩ := hg
    exact dicksonValue_siegel Q hQ u v hu huv
  | one => exact dicksonValue_one Q
  | mul x y hx hy ihx ihy =>
    have he := dicksonParity_mul_of_mem_reflectionSubgroup Q hQ x
      (elementary_le_reflections_stable Q hQ hd hx) y
    change dicksonValue Q (x*y) = dicksonValue Q x + dicksonValue Q y at he
    rw [he, ihx, ihy, add_zero]
  | inv x hx ih => rw [dicksonValue_inv, ih]
end Atlas.Orthogonal
