import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A solvable supplement to a normal subgroup of a perfect group forces
that normal subgroup to be the whole group. No particular action is assumed. -/
namespace Atlas.GroupTheory

theorem eq_top_of_perfect_normal_solvable_sup {G : Type*} [Group G]
    [Group.IsPerfect G] (N B : Subgroup G) [N.Normal] [Group.IsSolvable B]
    (h : N ⊔ B = ⊤) : N = ⊤ := by
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have hn : N.map f = ⊥ := by
    apply le_antisymm _ bot_le
    rintro q ⟨n, hn, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr hn
  have hb : B.map f = ⊤ := by
    have hh := congrArg (fun H : Subgroup G => H.map f) h
    rw [Subgroup.map_sup, hn, bot_sup_eq,
      Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective N)] at hh
    exact hh
  have hf : Function.Surjective (f.comp B.subtype) := by
    intro q
    have hq : q ∈ B.map f := hb ▸ Subgroup.mem_top q
    obtain ⟨b, hb, hq⟩ := hq
    exact ⟨⟨b, hb⟩, hq⟩
  letI : Group.IsSolvable (G ⧸ N) := Group.isSolvable_of_surjective hf
  have hs : Subsingleton (G ⧸ N) := by
    rcases subsingleton_or_nontrivial (G ⧸ N) with hs | hn
    · exact hs
    · exact False.elim (Group.IsPerfect.not_isSolvable (G ⧸ N) inferInstance)
  exact QuotientGroup.subgroup_eq_top_of_subsingleton N hs

theorem simple_of_perfect_solvable_normal_supplement {G : Type*}
    [Group G] [Nontrivial G] [Group.IsPerfect G]
    (B : Subgroup G) [Group.IsSolvable B]
    (h : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N ⊔ B = ⊤) : IsSimpleGroup G := by
  constructor
  intro N hN
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  · exact Or.inr (eq_top_of_perfect_normal_solvable_sup N B (h N hN hbot))

end Atlas.GroupTheory
