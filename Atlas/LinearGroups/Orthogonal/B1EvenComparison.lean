import Atlas.LinearGroups.Orthogonal.ProjectiveEvenB
import Atlas.LinearGroups.Symplectic.RankOne

/-! # Actual B₁/A₁ comparison in characteristic two -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

/-- The established polar-quotient B/C isomorphism and the marked rank-one Sp/SL map. -/
def evenB1EquivPSL2 : ProjectiveElementary (formB 1 F) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  (evenProjectiveBEquivPSp (by decide : 0 < 1)).trans Atlas.Symplectic.rankOnePSL

end Atlas.Orthogonal
