import Atlas.LinearGroups.Symplectic.Primitivity
import Atlas.LinearGroups.Symplectic.LineTransvections
import Atlas.LinearGroups.Symplectic.Noncommutative

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F] [Finite F]

/-- Iwasawa simplicity for the actual central quotient in every rank at least two,
with the unique higher-rank exception (rank, field order) = (2,2). -/
theorem simple_high_rank (hn : 2 ≤ n) (he : (n,Nat.card F) ≠ (2,2)) :
    IsSimpleGroup (PSp n F) := by
  let := projective_preprimitive (F := F) hn
  let := projective_nontrivial (F := F) (show 0 < n by omega)
  let := projective_perfect_of_good (Or.inr ⟨hn,he⟩ : Good n (Nat.card F))
  exact iwasawa.isSimpleGroup (Group.IsPerfect.commutator_eq_top (G := PSp n F)) inferInstance

end Atlas.Symplectic
