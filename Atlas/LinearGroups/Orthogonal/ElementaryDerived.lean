import Atlas.LinearGroups.Orthogonal.ElementaryQuotient
import Atlas.LinearGroups.Orthogonal.SiegelSpinor

/-! # Elementary and derived subgroup identification in odd characteristic and Witt index ≥2 -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
open scoped commutatorElement
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (H : WittTwoFrame Q)
  (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

include H hQ h2 in
theorem equal_norm_reflection_product_mem_commutator (a b : V) (ha : Q a ≠ 0)
    (hb : Q b ≠ 0) (hval : Q a = Q b) :
    reflectionElement Q b hb * reflectionElement Q a ha ∈ commutator (isometrySubgroup Q) := by
  obtain ⟨g, hg, hga⟩ := elementary_transport_equal_value Q H hQ h2 a b ha hval
  have hc : g * reflectionElement Q a ha * g⁻¹ = reflectionElement Q b hb := by
    simpa only [hga] using reflectionElement_conj Q g a ha
  have he : ⁅g, reflectionElement Q a ha⁆ =
      reflectionElement Q b hb * reflectionElement Q a ha := by
    rw [commutatorElement_def, reflectionElement_inv, hc]
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top _)

include H hQ h2 in
theorem anisotropic_siegel_mem_commutator (u v : V) (hu : Q u = 0)
    (huv : Q.polarBilin u v = 0) (hv : Q v ≠ 0) :
    siegelElement Q u v hu huv ∈ commutator (isometrySubgroup Q) := by
  rw [siegelElement_reflection_factor Q u v hu huv hv]
  exact equal_norm_reflection_product_mem_commutator Q H hQ h2 v (v+Q v • u) hv _
    (siegel_reflection_vector_value Q u v hu huv).symm

include H hQ h2 in
/-- An isotropic parameter splits into two anisotropic parameters in the same perpendicular space. -/
theorem isotropic_parameter_anisotropic_sum (u v : V) (hv : Q v = 0)
    (huv : Q.polarBilin u v = 0) :
    ∃ w₁ w₂, v = w₁+w₂ ∧ Q w₁ ≠ 0 ∧ Q w₂ ≠ 0 ∧
      Q.polarBilin u w₁ = 0 ∧ Q.polarBilin u w₂ = 0 := by
  obtain ⟨a, b, ha, hb, hab, hau, hbu⟩ := hyperbolic_pair_in_perpendicular Q H hQ h2 u
  let w := a+b
  have hw : Q w = 1 := by
    rw [QuadraticMap.map_add Q]
    change Q a + Q b + Q.polarBilin a b = 1
    rw [ha, hb, hab, zero_add, zero_add]
  have huw : Q.polarBilin u w = 0 := by
    change Q.polarBilin u (a+b) = 0
    rw [map_add, polar_swap Q u a, polar_swap Q u b, hau, hbu, add_zero]
  by_cases hd : Q (v-w) = 0
  · have hs : Q (v+w) = 2 := by
      have hm := sub_value Q v w
      have hp := QuadraticMap.map_add Q v w
      change Q (v+w) = Q v + Q w + Q.polarBilin v w at hp
      rw [hv, hw, hd] at hm
      rw [hv, hw] at hp
      linear_combination hp + hm
    refine ⟨-w, v+w, by abel, ?_, ?_, ?_, ?_⟩
    · rw [Q.map_neg, hw]; exact one_ne_zero
    · rw [hs]; exact h2
    · rw [map_neg, huw, neg_zero]
    · rw [map_add, huv, huw, add_zero]
  · refine ⟨w, v-w, by abel, by rw [hw]; exact one_ne_zero, hd, huw, ?_⟩
    rw [map_sub, huv, huw, sub_zero]

include H hQ h2 in
theorem siegel_mem_commutator (u v : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    siegelElement Q u v hu huv ∈ commutator (isometrySubgroup Q) := by
  by_cases hv : Q v = 0
  · obtain ⟨w₁, w₂, he, h₁, h₂, hu₁, hu₂⟩ :=
      isotropic_parameter_anisotropic_sum Q H hQ h2 u v hv huv
    have he' : siegelElement Q u v hu huv =
        siegelElement Q u w₁ hu hu₁ * siegelElement Q u w₂ hu hu₂ := by
      rw [siegelElement_add]
      simpa only [he]
    rw [he']
    exact (commutator (isometrySubgroup Q)).mul_mem
      (anisotropic_siegel_mem_commutator Q H hQ h2 u w₁ hu hu₁ h₁)
      (anisotropic_siegel_mem_commutator Q H hQ h2 u w₂ hu hu₂ h₂)
  · exact anisotropic_siegel_mem_commutator Q H hQ h2 u v hu huv hv

include H hQ h2 in
/-- The actual elementary subgroup equals the full-group derived subgroup in this range. -/
theorem elementary_eq_commutator : elementarySubgroup Q = commutator (isometrySubgroup Q) := by
  apply le_antisymm _ (commutator_le_elementary Q H hQ h2)
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, v, hu, huv, rfl⟩
  exact siegel_mem_commutator Q H hQ h2 u v hu huv

end Atlas.Orthogonal
