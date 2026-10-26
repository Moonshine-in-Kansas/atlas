import Atlas.GroupTheory.IwasawaStabilizer
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Iwasawa's argument with a solvable normal subgroup of a stabilizer.
The whole stabilizer need not be solvable, and the radical need not be abelian. -/
namespace Atlas.GroupTheory
variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPreprimitive G X]

theorem iwasawa_solvable_radical_simple [Nontrivial G] [Group.IsPerfect G]
    (a : X) (A : Subgroup G) [Group.IsSolvable A]
    (hA : A ≤ MulAction.stabilizer G a)
    (hAn : (A.subgroupOf (MulAction.stabilizer G a)).Normal)
    (hgen : Subgroup.normalClosure (A : Set G) = ⊤) : IsSimpleGroup G := by
  constructor
  intro N hN
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  letI := normal_pretransitive (X := X) N hbot
  have hsup := normal_sup_abelian_eq_top a A hA hAn hgen N
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have hn : N.map f = ⊥ := by
    apply le_antisymm _ bot_le
    intro q hq
    obtain ⟨n, hn, rfl⟩ := hq
    exact (QuotientGroup.eq_one_iff _).mpr hn
  have ha : A.map f = ⊤ := by
    have hh := congrArg (fun S : Subgroup G => S.map f) hsup
    rw [Subgroup.map_sup, hn, bot_sup_eq,
      Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective N)] at hh
    exact hh
  have hf : Function.Surjective (f.comp A.subtype) := by
    intro q
    have hq : q ∈ A.map f := ha ▸ Subgroup.mem_top q
    obtain ⟨a, ha, hq⟩ := hq
    exact ⟨⟨a, ha⟩, hq⟩
  letI : Group.IsSolvable (G ⧸ N) := Group.isSolvable_of_surjective hf
  have hsub : Subsingleton (G ⧸ N) := by
    rcases subsingleton_or_nontrivial (G ⧸ N) with h | h
    · exact h
    · exact False.elim (Group.IsPerfect.not_isSolvable (G ⧸ N) inferInstance)
  exact QuotientGroup.subgroup_eq_top_of_subsingleton N hsub

end Atlas.GroupTheory
