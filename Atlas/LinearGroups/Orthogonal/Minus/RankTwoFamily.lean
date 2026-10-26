import Atlas.LinearGroups.Orthogonal.Minus.Family
import Atlas.LinearGroups.Orthogonal.Minus.RankTwoOrder
import Atlas.LinearGroups.Orthogonal.Minus.RankTwoSimplicity

/-! Low-rank supplement for the retained public carrier; not a new catalogue family. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def family_rankTwo_equiv (hdeg : Module.finrank F K = 2) :
    DMinus 2 F K hdeg ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  rankTwoProjectiveEquiv hdeg

theorem family_rankTwo_order (hdeg : Module.finrank F K = 2) :
    Nat.card (DMinus 2 F K hdeg) =
      (Nat.card F ^ 2 * (Nat.card F ^ 2+1) * (Nat.card F ^ 2-1)) /
        Nat.gcd 4 (Nat.card F ^ 2+1) := rankTwo_projective_order_uniform hdeg

theorem family_rankTwo_simple (hdeg : Module.finrank F K = 2) :
    IsSimpleGroup (DMinus 2 F K hdeg) := rankTwo_simple hdeg

theorem family_rankTwo_noncommutative (hdeg : Module.finrank F K = 2) :
    ¬ IsMulCommutative (DMinus 2 F K hdeg) := rankTwo_noncommutative hdeg

end Atlas.Orthogonal.Minus
