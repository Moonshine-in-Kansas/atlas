import Mathlib.GroupTheory.Commutator.Basic

namespace Atlas.GroupTheory
open scoped commutatorElement

theorem normal_disjoint_normalizer_commute {G : Type*} [Group G]
    (H U : Subgroup G) [H.Normal] (hn : H ≤ Subgroup.normalizer U)
    (hd : Disjoint H U) {g x : G} (hg : g ∈ H) (hx : x ∈ U) :
    Commute g x := by
  apply commutatorElement_eq_one_iff_commute.mp
  have hc := Subgroup.commutator_mem_commutator hg hx
  exact Subgroup.mem_bot.mp (hd.le_bot
    ⟨Subgroup.commutator_le_left H U hc,
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hn) hc⟩)

end Atlas.GroupTheory
