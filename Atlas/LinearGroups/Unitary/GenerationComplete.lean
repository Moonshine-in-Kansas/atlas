import Atlas.LinearGroups.Unitary.RankOneGenerationAll
import Atlas.LinearGroups.Unitary.Family

/-! Uniform transvection generation, including the nonsimple rank-one groups. -/
noncomputable section
namespace Atlas.Unitary
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem transvectionGenerated_eq_top_of_not_three_binary
    (hdeg : Module.finrank F K = 2) {n : ℕ} (hn : 2 ≤ n)
    (hne : (n, Nat.card F) ≠ (3, 2)) : transvectionGenerated hdeg (n := n) = ⊤ := by
  by_cases he : n = 2
  · subst n
    exact transvectionGenerated_two_eq_top hdeg
  apply transvectionGenerated_eq_top_of_good hdeg
  exact ⟨hn, fun h => he (congrArg Prod.fst h), fun h => he (congrArg Prod.fst h), hne⟩
end Atlas.Unitary
