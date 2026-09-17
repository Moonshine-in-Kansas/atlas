import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

noncomputable section
namespace Atlas.Combinatorics
open scoped BigOperators

/-- Count incidences of selected blocks with k-subsets of a fixed marked set. -/
theorem subblock_incidence_sum {V : Type*} [DecidableEq V]
    (blocks : Finset (Finset V)) (O : Finset V) (k : ℕ) :
    (∑ B ∈ blocks, (B ∩ O).card.choose k) =
      ∑ U ∈ O.powersetCard k, (blocks.filter (fun B => U ⊆ B)).card := by
  classical
  have he (B : Finset V) : (B ∩ O).powersetCard k =
      (O.powersetCard k).filter (fun U => U ⊆ B) := by
    ext U
    simp only [Finset.mem_powersetCard,Finset.mem_filter,Finset.subset_inter_iff]
    tauto
  have hc (B : Finset V) : (B ∩ O).card.choose k =
      ∑ U ∈ O.powersetCard k, if U ⊆ B then 1 else 0 := by
    rw [← Finset.card_powersetCard,he,Finset.card_filter]
  simp_rw [hc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U _
  rw [Finset.card_filter]

/-- Constant replication turns the incidence identity into a numerical moment. -/
theorem subblock_incidence_count {V : Type*} [DecidableEq V]
    (blocks : Finset (Finset V)) (O : Finset V) (k l : ℕ)
    (h : ∀ U ∈ O.powersetCard k, (blocks.filter (fun B => U ⊆ B)).card = l) :
    (∑ B ∈ blocks, (B ∩ O).card.choose k) = O.card.choose k * l := by
  rw [subblock_incidence_sum,Finset.sum_congr rfl h]
  simp

end Atlas.Combinatorics
