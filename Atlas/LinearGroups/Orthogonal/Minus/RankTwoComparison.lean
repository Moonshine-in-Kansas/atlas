import Atlas.LinearGroups.Orthogonal.Minus.RankTwoGeneration
import Atlas.LinearGroups.Orthogonal.Minus.RankTwoImage
import Atlas.LinearGroups.Orthogonal.Minus.RankTwoScalarKernel

/-! Actual rank-two comparison, with trivial scalar intersection proved before simplicity. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Matrix
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def rankTwoElementaryEquiv (hdeg : Module.finrank F K = 2) :
    ProjectiveSpecialLinearGroup (Fin 2) K ≃* E hdeg 1 :=
  (hermitianImageEquiv hdeg).trans
    (MulEquiv.subgroupCongr (hermitianHom_range_eq_elementary hdeg))

theorem rankTwo_scalar_bot (hdeg : Module.finrank F K = 2) :
    elementaryScalarSubgroup (form hdeg 1) = ⊥ := by
  apply bot_unique
  rintro g ⟨c,hc,hg⟩
  obtain ⟨a,ha⟩ := (hermitianHom_range_eq_elementary hdeg).ge g.prop
  have hc1 : c=1 := hermitianHom_scalar_factor hdeg a c (by
    intro v
    rw [ha]
    exact hg v)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simpa [hc1] using hg v

def rankTwoProjectiveElementaryEquiv (hdeg : Module.finrank F K = 2) :
    ProjectiveElementary (form hdeg 1) ≃* E hdeg 1 :=
  (QuotientGroup.quotientMulEquivOfEq (rankTwo_scalar_bot hdeg)).trans
    (QuotientGroup.quotientBot)

/-- The actual projective minus carrier is equivalent to PSL over the quadratic extension. -/
def rankTwoProjectiveEquiv (hdeg : Module.finrank F K = 2) :
    ProjectiveElementary (form hdeg 1) ≃* ProjectiveSpecialLinearGroup (Fin 2) K :=
  (rankTwoProjectiveElementaryEquiv hdeg).trans (rankTwoElementaryEquiv hdeg).symm

theorem rankTwo_elementary_order (hdeg : Module.finrank F K = 2) :
    Nat.card (E hdeg 1) = (Nat.card F ^ 2 * ((Nat.card F ^ 2)^2 - 1)) /
      Nat.gcd 2 (Nat.card F ^ 2 - 1) := by
  rw [← hermitianHom_range_eq_elementary hdeg]
  exact card_hermitian_image hdeg

theorem rankTwo_projective_order (hdeg : Module.finrank F K = 2) :
    Nat.card (ProjectiveElementary (form hdeg 1)) =
      (Nat.card F ^ 2 * ((Nat.card F ^ 2)^2 - 1)) /
        Nat.gcd 2 (Nat.card F ^ 2 - 1) := by
  rw [Nat.card_congr (rankTwoProjectiveElementaryEquiv hdeg).toEquiv]
  exact rankTwo_elementary_order hdeg

end Atlas.Orthogonal.Minus
