import Atlas.LinearGroups.Orthogonal.Minus.RankTwoHermitianKernel

/-! The actual image of Hermitian congruence, before elementary-image identification.
Its equivalence and order use the constructed map and its exact kernel. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic Matrix
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem hermitianProjectiveHom_range (hdeg : Module.finrank F K = 2) :
    (hermitianProjectiveHom hdeg).range = (hermitianHom hdeg).range := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (SpecialLinearGroup (Fin 2) K)) a
    exact ⟨b,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨QuotientGroup.mk a,rfl⟩

def hermitianImageEquiv (hdeg : Module.finrank F K = 2) :
    ProjectiveSpecialLinearGroup (Fin 2) K ≃* (hermitianHom hdeg).range :=
  (MonoidHom.ofInjective (hermitianProjectiveHom_injective hdeg)).trans
    (MulEquiv.subgroupCongr (hermitianProjectiveHom_range hdeg))

theorem card_hermitian_image (hdeg : Module.finrank F K = 2) :
    Nat.card (hermitianHom hdeg).range =
      (Nat.card F ^ 2 * ((Nat.card F ^ 2)^2 - 1)) /
        Nat.gcd 2 (Nat.card F ^ 2 - 1) := by
  rw [← Nat.card_congr (hermitianImageEquiv hdeg).toEquiv, Atlas.card_psl_factor 2]
  simp [card_extension hdeg]

end Atlas.Orthogonal.Minus
