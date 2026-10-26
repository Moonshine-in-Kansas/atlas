import Atlas.LinearGroups.Symplectic.RankOne

/-! The existing rank-one matrix and full-center quotient comparisons. -/
noncomputable section
namespace Atlas.Comparisons.Classical
variable {F : Type*} [Field F]

/-- Lie rank one, over any field. -/
def c1EquivA1 : Atlas.Symplectic.PSp 1 F ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := Atlas.Symplectic.rankOnePSL

@[simp] theorem c1EquivA1_projection (g : Atlas.Symplectic.Sp 1 F) :
    c1EquivA1 (Atlas.Symplectic.projection g) =
      QuotientGroup.mk (Atlas.Symplectic.rankOneSL g) := rfl
end Atlas.Comparisons.Classical
