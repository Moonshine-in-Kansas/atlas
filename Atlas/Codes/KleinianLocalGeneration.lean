/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Codes.HexacodeConjugation

namespace Atlas.Codes

theorem klein_subgroup_full (R : Subgroup KIsometry) (hκ : localKappa ∈ R)
    (X : KIsometry) (hX : X ∈ R) (hn : X ≠ 1 ∧ X ≠ localKappa ∧ X ≠ localKappa⁻¹) : R = ⊤ := by
  have hU : localU ∈ R := by
    rcases kIsometry_eq_six X with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hn.1 rfl)
    · exact hX
    · have he : localKappa⁻¹ * localV = localU := kIsometry_ext_ab (by decide) (by decide)
      exact he ▸ R.mul_mem (R.inv_mem hκ) hX
    · have he : localKappa * localW = localU := kIsometry_ext_ab (by decide) (by decide)
      exact he ▸ R.mul_mem hκ hX
    · exact False.elim (hn.2.1 rfl)
    · exact False.elim (hn.2.2 rfl)
  apply top_unique
  intro L _
  rcases kIsometry_eq_six L with rfl | rfl | rfl | rfl | rfl | rfl
  · exact R.one_mem
  · exact hU
  · have he : localKappa * localU = localV := kIsometry_ext_ab (by decide) (by decide)
    exact he ▸ R.mul_mem hκ hU
  · have he : localKappa⁻¹ * localU = localW := kIsometry_ext_ab (by decide) (by decide)
    exact he ▸ R.mul_mem (R.inv_mem hκ) hU
  · exact hκ
  · exact R.inv_mem hκ

theorem klein_cycle_inverter_noncyclic (P X : KIsometry)
    (hP : P = localKappa ∨ P = localKappa⁻¹) (hx : X * P * X⁻¹ = P⁻¹) :
    X ≠ 1 ∧ X ≠ localKappa ∧ X ≠ localKappa⁻¹ := by
  rcases hP with rfl | rfl
  all_goals
    refine ⟨?_,?_,?_⟩
    all_goals
      intro he
      rw [he] at hx
      have hh := LinearEquiv.congr_fun hx a
      exact (by decide : _ ≠ _) hh

theorem klein_subgroup_full_of_inverter (R : Subgroup KIsometry) (P X : KIsometry)
    (hP : P = localKappa ∨ P = localKappa⁻¹) (hp : P ∈ R) (hx : X ∈ R)
    (hi : X * P * X⁻¹ = P⁻¹) : R = ⊤ := by
  have hκ : localKappa ∈ R := by
    rcases hP with rfl | rfl
    · exact hp
    · simpa only [inv_inv] using R.inv_mem hp
  exact klein_subgroup_full R hκ X hx (klein_cycle_inverter_noncyclic P X hP hi)

end Atlas.Codes
