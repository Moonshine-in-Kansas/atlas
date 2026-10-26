import Atlas.LinearGroups.Orthogonal.Minus.WittFrame
import Atlas.LinearGroups.Orthogonal.Minus.StandardComplement
import Atlas.LinearGroups.Orthogonal.PerfectAllCharD

/-! Stable perfectness of the actual elementary minus group, in every characteristic. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem elementary_perfect (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Group.IsPerfect (E hdeg (n+3)) :=
  elementary_perfect_of_complements_all_char _ (polar_nondegenerate hdeg _)
    (form hdeg (n+2)) (wittTwoFrame hdeg n) (polar_nondegenerate hdeg _)
    (fun e f he hf hef => complement_isometry hdeg e f he hf hef)

end Atlas.Orthogonal.Minus
