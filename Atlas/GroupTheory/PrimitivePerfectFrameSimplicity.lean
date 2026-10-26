import Atlas.GroupTheory.PrimitiveNormal
import Atlas.GroupTheory.PerfectSimpleQuotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! A normal-subgroup simplicity argument using a perfect odd-index subgroup,
a simple quotient of that subgroup, and one additional involution. -/
namespace Atlas.GroupTheory
open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

theorem stabilizer_quotient_surjective_of_normal_transitive (N : Subgroup G) [N.Normal]
    [IsPretransitive N X] (x : X) :
    Function.Surjective ((QuotientGroup.mk' N).comp (stabilizer G x).subtype) := by
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N q
  obtain ⟨n,hn⟩ := exists_smul_eq N x (g • x)
  have hs : (n : G)⁻¹*g∈stabilizer G x := by
    change ((n : G)⁻¹*g) • x=x
    rw [mul_smul,←hn]
    exact inv_smul_smul (n : G) x
  refine ⟨⟨(n : G)⁻¹*g,hs⟩,?_⟩
  change (QuotientGroup.mk' N) ((n : G)⁻¹*g)=(QuotientGroup.mk' N) g
  have hnq : (QuotientGroup.mk' N) (n : G)=1 := (QuotientGroup.eq_one_iff _).mpr n.prop
  simp only [map_mul,map_inv,hnq,inv_one,one_mul]

theorem normal_quotient_card_dvd_stabilizer [FaithfulSMul G X] [IsPreprimitive G X]
    (N : Subgroup G) [N.Normal] (hN : N≠⊥) (x : X) :
    Nat.card (G ⧸ N) ∣ Nat.card (stabilizer G x) := by
  let := normal_pretransitive (X := X) N hN
  exact Subgroup.card_dvd_of_surjective _ (stabilizer_quotient_surjective_of_normal_transitive N x)

theorem normal_eq_top_of_odd_index_involution [Finite G]
    (H : Subgroup G) (hodd : Odd H.index) (t : G) (ht : t^2=1)
    (hgen : H ⊔ Subgroup.zpowers t=⊤)
    (N : Subgroup G) [N.Normal] (hHN : H≤N) : N=⊤ := by
  let f := QuotientGroup.mk' N
  have hmap : H.map f=⊥ := by
    apply le_antisymm _ bot_le
    rintro q ⟨h,hh,rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr (hHN hh)
  have hz : Subgroup.zpowers (f t)=⊤ := by
    have hm := congrArg (Subgroup.map f) hgen
    rw [Subgroup.map_sup,hmap,f.map_zpowers,bot_sup_eq,←MonoidHom.range_eq_map,
      MonoidHom.range_eq_top_of_surjective f (QuotientGroup.mk'_surjective N)] at hm
    exact hm
  have hc2 : Nat.card (G ⧸ N) ∣ 2 := by
    rw [←orderOf_eq_card_of_zpowers_eq_top hz]
    apply orderOf_dvd_of_pow_eq_one
    rw [←map_pow,ht,map_one]
  have hci : Nat.card (G ⧸ N) ∣ H.index := Subgroup.index_dvd_of_le hHN
  have ho : Odd (Nat.card (G ⧸ N)) := hodd.of_dvd_nat hci
  have hc : Nat.card (G ⧸ N)=1 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hc2 with h|h
    · exact h
    · rw [h] at ho
      obtain ⟨k,hk⟩ := ho
      omega
  exact QuotientGroup.subgroup_eq_top_of_subsingleton N
    (Nat.card_eq_one_iff_unique.mp hc).1

theorem simple_of_primitive_perfect_frame [Finite G] [Nontrivial G]
    [FaithfulSMul G X] [IsPreprimitive G X]
    (H : Subgroup G) [Group.IsPerfect H]
    {S : Type*} [Group S] [IsSimpleGroup S]
    (π : H →* S) (hπ : Function.Surjective π) [Group.IsSolvable π.ker]
    (p : ℕ) (hp : p ∣ Nat.card S) (x : X)
    (hx : ¬p ∣ Nat.card (stabilizer G x))
    (hodd : Odd H.index) (t : G) (ht : t^2=1)
    (hgen : H ⊔ Subgroup.zpowers t=⊤) : IsSimpleGroup G := by
  constructor
  intro N hnormal
  by_cases hN : N=⊥
  · exact Or.inl hN
  right
  have hq : ¬p ∣ Nat.card (G ⧸ N) := fun h =>
    hx (h.trans (normal_quotient_card_dvd_stabilizer N hN x))
  have hf := perfect_hom_trivial_of_simple_quotient π hπ
    ((QuotientGroup.mk' N).comp H.subtype) p hp hq
  have hHN : H≤N := by
    intro h hh
    exact (QuotientGroup.eq_one_iff h).mp (hf ⟨h,hh⟩)
  exact normal_eq_top_of_odd_index_involution H hodd t ht hgen N hHN

end Atlas.GroupTheory
