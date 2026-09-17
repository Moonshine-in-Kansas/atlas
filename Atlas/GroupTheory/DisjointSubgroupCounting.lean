import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

noncomputable section
namespace Atlas.GroupTheory
variable {G ι : Type*} [Group G]

theorem subgroup_nonidentity_sigma_injective (H : ι → Subgroup G)
    (hH : Pairwise (fun i j => Disjoint (H i) (H j))) :
    Function.Injective (fun x : (Σi,{g : H i // g≠1}) => x.2.val.val) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ hxy
  change x.val.val=y.val.val at hxy
  have hij : i=j := by
    by_contra hn
    have hx : x.val.val=1 := (Subgroup.disjoint_def.mp (hH hn))
      x.val.prop (by rw [hxy]; exact y.val.prop)
    exact x.prop (Subtype.ext hx)
  subst j
  congr 1
  exact Subtype.ext (Subtype.ext hxy)

theorem card_subgroup_nonidentity [Finite G] (H : Subgroup G) :
    Nat.card {x : H // x≠1}=Nat.card H-1 := by
  classical
  letI := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp [Nat.card_eq_fintype_card]

theorem disjoint_subgroup_nonidentity_card_bound [Finite G] [Fintype ι]
    (H : ι → Subgroup G) (hH : Pairwise (fun i j => Disjoint (H i) (H j))) :
    (∑i,(Nat.card (H i)-1)) ≤ Nat.card G := by
  classical
  have hi := Nat.card_le_card_of_injective _ (subgroup_nonidentity_sigma_injective H hH)
  have hc : Nat.card (Σi,{g : H i // g≠1})=∑i,(Nat.card (H i)-1) := by
    letI (i : ι) := Fintype.ofFinite {g : H i // g≠1}
    rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [←Nat.card_eq_fintype_card,card_subgroup_nonidentity]
  rwa [hc] at hi

end Atlas.GroupTheory

namespace Atlas.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem subgroups_prime_card_disjoint {p : ℕ} (hp : p.Prime)
    (H K : Subgroup G) (hH : Nat.card H=p) (hK : Nat.card K=p) (hne : H≠K) : Disjoint H K := by
  apply Subgroup.disjoint_def.mpr
  intro x hxH hxK
  by_contra hx
  have hd : orderOf x∣p := by
    rw [←hH,Subgroup.orderOf_coe (⟨x,hxH⟩ : H)]
    exact orderOf_dvd_natCard _
  have ho : orderOf x=p := by
    rcases (Nat.dvd_prime hp).mp hd with he|he
    · exact (hx (orderOf_eq_one_iff.mp he)).elim
    · exact he
  have hZ : Nat.card (Subgroup.zpowers x)=p := by rw [Nat.card_zpowers,ho]
  have hZH : Subgroup.zpowers x=H := Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hxH) (by rw [hZ,hH])
  have hZK : Subgroup.zpowers x=K := Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hxK) (by rw [hZ,hK])
  exact hne (hZH.symm.trans hZK)

end Atlas.GroupTheory
