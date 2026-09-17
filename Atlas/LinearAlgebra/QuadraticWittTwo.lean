import Atlas.LinearAlgebra.QuadraticPerpHyperbolic
import Atlas.LinearAlgebra.QuadraticTransitivity
import Atlas.LinearAlgebra.QuadraticSiegel

/-! # Two actual hyperbolic pairs supply hyperbolic planes in polar hyperplanes -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Two perpendicular hyperbolic pairs in the actual quadratic space. -/
structure WittTwoFrame (Q : QuadraticForm F V) where
  e₁ : V
  f₁ : V
  e₂ : V
  f₂ : V
  qe₁ : Q e₁ = 0
  qf₁ : Q f₁ = 0
  qe₂ : Q e₂ = 0
  qf₂ : Q f₂ = 0
  pair₁ : Q.polarBilin e₁ f₁ = 1
  pair₂ : Q.polarBilin e₂ f₂ = 1
  ee : Q.polarBilin e₂ e₁ = 0
  ef : Q.polarBilin e₂ f₁ = 0
  fe : Q.polarBilin f₂ e₁ = 0
  ff : Q.polarBilin f₂ f₁ = 0

variable (Q : QuadraticForm F V) (H : WittTwoFrame Q)

theorem WittTwoFrame.first_ne_zero : H.e₁ ≠ 0 := by
  intro h
  have hp := H.pair₁
  rw [h, map_zero, LinearMap.zero_apply] at hp
  exact zero_ne_one hp

theorem WittTwoFrame.second_not_multiple (c : F) : H.e₂ ≠ c • H.e₁ := by
  intro h
  have hc := H.ef
  rw [h, map_smul, LinearMap.smul_apply, smul_eq_mul, H.pair₁, mul_one] at hc
  have hp := H.pair₂
  rw [h, hc, zero_smul, map_zero, LinearMap.zero_apply] at hp
  exact zero_ne_one hp

include H in
/-- Every polar hyperplane contains a hyperbolic plane in odd characteristic and Witt index ≥2. -/
theorem hyperbolic_pair_in_perpendicular (hQ : Q.polarBilin.Nondegenerate)
    (h2 : (2 : F) ≠ 0) (d : V) :
    ∃ a b, Q a = 0 ∧ Q b = 0 ∧ Q.polarBilin a b = 1 ∧
      Q.polarBilin a d = 0 ∧ Q.polarBilin b d = 0 := by
  by_cases hd0 : d = 0
  · subst d
    exact ⟨H.e₁, H.f₁, H.qe₁, H.qf₁, H.pair₁, by simp, by simp⟩
  by_cases hqd : Q d = 0
  · have hrad : Q.radical = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      exact (Submodule.mem_bot F).mpr (hQ.1 x (fun y => LinearMap.congr_fun hx.2 y))
    obtain ⟨g, hg⟩ := exists_isometry_singular Q hrad d H.e₁ hd0
      (WittTwoFrame.first_ne_zero Q H) hqd H.qe₁
    refine ⟨g.symm H.e₂, g.symm H.f₂, (g.symm.map_app _).trans H.qe₂,
      (g.symm.map_app _).trans H.qf₂, ?_, ?_, ?_⟩
    · exact (isometry_polar Q g.symm _ _).trans H.pair₂
    · have h := isometry_polar Q g (g.symm H.e₂) d
      rw [g.apply_symm_apply, hg] at h
      exact h.symm.trans H.ee
    · have h := isometry_polar Q g (g.symm H.f₂) d
      rw [g.apply_symm_apply, hg] at h
      exact h.symm.trans H.fe
  · obtain ⟨a, hane, ha, had⟩ := isotropic_plane_perpendicular Q H.e₁ H.e₂ d
      H.qe₁ H.qe₂ ((polar_swap Q _ _).trans H.ee)
      (WittTwoFrame.first_ne_zero Q H) (WittTwoFrame.second_not_multiple Q H)
    have hdd : Q.polarBilin d d ≠ 0 := by rw [polar_self]; exact mul_ne_zero h2 hqd
    obtain ⟨b, hb, hab, hbd⟩ := perpendicular_hyperbolic_partner Q hQ d a hdd ha hane had
    exact ⟨a, b, ha, hb, hab, had, hbd⟩

end Atlas.Quadratic
