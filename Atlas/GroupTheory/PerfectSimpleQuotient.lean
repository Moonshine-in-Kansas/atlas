import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Index

/-! A perfect group with soluble kernel and simple quotient has no image in a
finite group whose order misses a divisor of that simple quotient. -/
namespace Atlas.GroupTheory

variable {H S Q : Type*} [Group H] [Group S] [Group Q]

theorem perfect_hom_trivial_of_simple_quotient [Group.IsPerfect H] [IsSimpleGroup S]
    (π : H →* S) (hπ : Function.Surjective π) [Group.IsSolvable π.ker]
    (f : H →* Q) (p : ℕ) (hp : p ∣ Nat.card S) (hq : ¬p ∣ Nat.card Q) :
    ∀h : H,f h=1 := by
  let : (f.ker.map π).Normal := (inferInstance : f.ker.Normal).map π hπ
  rcases (inferInstance : (f.ker.map π).Normal).eq_bot_or_eq_top with hb|ht
  · have hle : f.ker≤π.ker := by
      intro h hh
      have hm : π h∈f.ker.map π := ⟨h,hh,rfl⟩
      rw [hb] at hm
      exact hm
    let φ : H ⧸ f.ker →* S := QuotientGroup.lift _ π hle
    have hφ : Function.Surjective φ := by
      intro s
      obtain ⟨h,rfl⟩ := hπ s
      exact ⟨QuotientGroup.mk h,rfl⟩
    have hd : Nat.card S ∣ Nat.card f.range := by
      have hd := Subgroup.card_dvd_of_surjective φ hφ
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hd
      exact hd
    exact fun _ => False.elim (hq (hp.trans (hd.trans (Subgroup.card_subgroup_dvd_card _))))
  · let fP : π.ker →* f.range :=
      { toFun := fun h => ⟨f h.val,⟨h.val,rfl⟩⟩
        map_one' := Subtype.ext (map_one f)
        map_mul' := fun a b => Subtype.ext (map_mul f a.val b.val) }
    have hfP : Function.Surjective fP := by
      rintro ⟨q,h,hq⟩
      have hm : π h∈f.ker.map π := by rw [ht];trivial
      obtain ⟨k,hk,hkh⟩ := hm
      have he : k⁻¹*h∈π.ker := by
        change π (k⁻¹*h)=1
        rw [map_mul,map_inv,hkh,inv_mul_cancel]
      refine ⟨⟨k⁻¹*h,he⟩,?_⟩
      apply Subtype.ext
      change f (k⁻¹*h)=q
      rw [map_mul,map_inv,show f k=1 from hk,inv_one,one_mul,hq]
    let : Group.IsSolvable f.range := Group.isSolvable_of_surjective hfP
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    have hsub : Subsingleton f.range := by
      rcases subsingleton_or_nontrivial f.range with hs|hn
      · exact hs
      · exact False.elim (Group.IsPerfect.not_isSolvable f.range inferInstance)
    intro h
    exact congrArg Subtype.val (hsub.elim (f.rangeRestrict h) 1)

end Atlas.GroupTheory
