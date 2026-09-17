import Atlas.LinearGroups.Symplectic.PerfectThree
import Atlas.LinearGroups.Symplectic.PerfectTwo

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F] [Finite F]

/-- All three field branches of perfectness, including the small fields. -/
theorem perfect_of_good (h : Good n (Nat.card F)) : Group.IsPerfect (Sp n F) := by
  by_cases hq : 3 < Nat.card F
  · exact perfect_of_card_gt_three hq
  have hq₂ : 2 ≤ Nat.card F := by
    let := Fintype.ofFinite F
    simpa only [Nat.card_eq_fintype_card] using (Nat.succ_le_of_lt (Fintype.one_lt_card (α := F)))
  have hn : 2 ≤ n := by
    rcases h with h|h
    · exact False.elim (hq h.2)
    · exact h.1
  rcases (show Nat.card F = 2 ∨ Nat.card F = 3 by omega) with h2|h3
  · apply perfect_of_card_two (by
      rcases h with h|h
      · omega
      · have hne : n ≠ 2 := by intro hn2; exact h.2 (Prod.ext hn2 h2)
        omega) h2
  · exact perfect_of_card_three hn h3

theorem projective_perfect_of_good (h : Good n (Nat.card F)) : Group.IsPerfect (PSp n F) := by
  let := perfect_of_good h
  infer_instance

end Atlas.Symplectic
