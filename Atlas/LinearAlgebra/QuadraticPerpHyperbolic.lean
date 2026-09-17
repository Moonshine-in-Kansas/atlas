import Atlas.LinearAlgebra.QuadraticHyperbolic
import Mathlib.Tactic.FieldSimp

/-! # Hyperbolic planes perpendicular to an anisotropic vector -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- An isotropic plane meets any polar hyperplane in a nonzero singular vector. -/
theorem isotropic_plane_perpendicular (e₁ e₂ d : V)
    (he₁ : Q e₁ = 0) (he₂ : Q e₂ = 0) (he₁₂ : Q.polarBilin e₁ e₂ = 0)
    (hne : e₁ ≠ 0) (hind : ∀ c : F, e₂ ≠ c • e₁) :
    ∃ a, a ≠ 0 ∧ Q a = 0 ∧ Q.polarBilin a d = 0 := by
  by_cases h : Q.polarBilin e₁ d = 0
  · exact ⟨e₁, hne, he₁, h⟩
  · let c := Q.polarBilin e₂ d / Q.polarBilin e₁ d
    refine ⟨e₂-c • e₁, ?_, ?_, ?_⟩
    · exact sub_ne_zero.mpr (hind c)
    · rw [sub_eq_add_neg, ← neg_smul, add_smul, he₁, he₂, polar_swap Q e₂ e₁, he₁₂]
      ring
    · rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact sub_eq_zero.mpr (div_mul_cancel₀ _ h).symm

/-- A singular vector perpendicular to a nonsingular line has a hyperbolic partner there. -/
theorem perpendicular_hyperbolic_partner (hQ : Q.polarBilin.Nondegenerate)
    (d a : V) (hd : Q.polarBilin d d ≠ 0) (ha : Q a = 0)
    (hne : a ≠ 0) (had : Q.polarBilin a d = 0) :
    ∃ b, Q b = 0 ∧ Q.polarBilin a b = 1 ∧ Q.polarBilin b d = 0 := by
  obtain ⟨b₀, hb₀⟩ := exists_normalized_partner Q a (fun h => hne (hQ.1 a h))
  let b₁ := b₀ - (Q.polarBilin b₀ d / Q.polarBilin d d) • d
  have hab : Q.polarBilin a b₁ = 1 := by
    dsimp [b₁]
    rw [map_sub, map_smul, had, smul_zero, sub_zero, hb₀]
  have hbd : Q.polarBilin b₁ d = 0 := by
    dsimp [b₁]
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      div_mul_cancel₀ _ hd, sub_self]
  refine ⟨b₁ - Q b₁ • a, (partner_correction Q a b₁ ha hab).1,
    (partner_correction Q a b₁ ha hab).2, ?_⟩
  rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, had, smul_zero, sub_zero, hbd]

end Atlas.Quadratic
