import Atlas.LinearGroups.Symplectic.SimplicityHighRank
import Atlas.LinearGroups.Symplectic.RankOne
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F] [Finite F]

theorem simple_rank_one (hq : 3 < Nat.card F) : IsSimpleGroup (PSp 1 F) := by
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) (show 4 ≤ Nat.card F by omega)
  exact rankOnePSL.isSimpleGroup

/-- Uniform positive simplicity in the full intended range, including the small fields. -/
theorem simple_of_good (h : Good n (Nat.card F)) : IsSimpleGroup (PSp n F) := by
  rcases h with ⟨rfl,hq⟩|⟨hn,he⟩
  · exact simple_rank_one hq
  · exact simple_high_rank hn he

end Atlas.Symplectic
