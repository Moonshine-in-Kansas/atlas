import F4Work.PositiveRootTail

/-! Separate group-level layer of the rho normalizer proof.
The prior statements and proof bodies are preserved; verification is recorded separately. -/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Atlas.GroupTheory

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem positiveLongFactor_mem_tail {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : Fin 4) (u : F) :
    positiveLongFactor hcard k u ∈ positiveRootTailSubgroup hcard := by
  apply ((subgroupListJoin_le_iff ((positiveRootFactorList hcard).tail)
    (positiveRootTailSubgroup hcard)).mp le_rfl)
      (alternatingLongRootHom hcard k).range
      (by fin_cases k <;> simp [positiveRootFactorList])
  exact ⟨Multiplicative.ofAdd u, rfl⟩

theorem positiveShortFactor_succ_mem_tail {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : Fin 3) (a b : F) :
    positiveShortFactor hcard k.succ a b ∈ positiveRootTailSubgroup hcard := by
  apply ((subgroupListJoin_le_iff ((positiveRootFactorList hcard).tail)
    (positiveRootTailSubgroup hcard)).mp le_rfl)
      (alternatingShortRootHom hcard k.succ).range
      (by fin_cases k <;> simp [positiveRootFactorList])
  exact ⟨shortRootParameters m hcard (a, b), rfl⟩

end Atlas.ReeF4
