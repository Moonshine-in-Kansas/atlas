import Atlas.LinearGroups.Symplectic.Nontrivial
import Atlas.LinearGroups.Symplectic.Perfectness

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F] [Finite F]

/-- Noncommutativity on the intended simplicity range, independently of simplicity itself. -/
theorem projective_not_commutative (h : Good n (Nat.card F)) :
    ¬ IsMulCommutative (PSp n F) := by
  have hn : 0 < n := by rcases h with h|h <;> omega
  let := projective_nontrivial (F := F) hn
  let := projective_perfect_of_good h
  exact Group.IsPerfect.not_isMulCommutative (PSp n F)

end Atlas.Symplectic
