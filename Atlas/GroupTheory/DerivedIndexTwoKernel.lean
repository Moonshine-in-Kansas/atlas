import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Index
import Lean.Elab.Tactic.Omega

namespace Atlas.GroupTheory

/-- A nontrivial abelian character identifies the derived subgroup before
any simplicity argument: noncommutativity and the normal-index bound force
the derived subgroup to have index two, leaving no larger proper kernel. -/
theorem commutator_eq_ker_and_index_two {J A : Type*}
    [Group J] [Finite J] [CommGroup A]
    (hnonabelian : ¬IsMulCommutative J)
    (hnormal : ∀ N : Subgroup J, N.Normal → N ≠ ⊥ → N.index ≤ 2)
    (f : J →* A) (hf : ∃ x : J, f x ≠ 1) :
    commutator J = f.ker ∧ (commutator J).index = 2 := by
  have hnontrivial : commutator J ≠ ⊥ :=
    fun h => hnonabelian ((commutator_eq_bot_iff J).mp h)
  have hle : commutator J ≤ f.ker := Abelianization.commutator_subset_ker f
  have hker : f.ker ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := hf
    apply hx
    have hxker : x ∈ f.ker := by rw [h]; trivial
    exact hxker
  have hproper : commutator J ≠ ⊤ := by
    intro h
    exact hker (top_unique (h ▸ hle))
  have hupper := hnormal (commutator J) inferInstance hnontrivial
  have hlower := (commutator J).one_lt_index_of_ne_top hproper
  have hindex : (commutator J).index = 2 := by omega
  refine ⟨?_, hindex⟩
  by_contra hne
  have hstrict := Subgroup.index_strictAnti (lt_of_le_of_ne hle hne)
  have hkindex := f.ker.one_lt_index_of_ne_top hker
  omega

/-- The actual derived subgroup has half the ambient order, independently
of its simplicity. The multiplicative form avoids truncated division. -/
theorem commutator_card_mul_two {J A : Type*}
    [Group J] [Finite J] [CommGroup A]
    (hnonabelian : ¬IsMulCommutative J)
    (hnormal : ∀ N : Subgroup J, N.Normal → N ≠ ⊥ → N.index ≤ 2)
    (f : J →* A) (hf : ∃ x : J, f x ≠ 1) :
    Nat.card (commutator J) * 2 = Nat.card J := by
  have hi := (commutator_eq_ker_and_index_two hnonabelian hnormal f hf).2
  simpa only [hi] using (commutator J).card_mul_index

/-- The character image has order two; surjectivity onto a larger abelian
target is neither assumed nor concluded. -/
theorem character_range_card_two {J A : Type*}
    [Group J] [Finite J] [CommGroup A]
    (hnonabelian : ¬IsMulCommutative J)
    (hnormal : ∀ N : Subgroup J, N.Normal → N ≠ ⊥ → N.index ≤ 2)
    (f : J →* A) (hf : ∃ x : J, f x ≠ 1) :
    Nat.card f.range = 2 := by
  obtain ⟨he, hi⟩ := commutator_eq_ker_and_index_two hnonabelian hnormal f hf
  rw [← Subgroup.index_ker f, ← he]
  exact hi

end Atlas.GroupTheory
