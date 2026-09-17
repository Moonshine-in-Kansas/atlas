import Atlas.Fischer.BasicQuotientSeparation
import Mathlib.GroupTheory.Subgroup.Centralizer

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- For all other primes the possible product orders two and three survive,
so an identified pair must already be equal. -/
theorem basic_quotient_separation_other {H : Type*} [Group H]
    (p : ℕ) [Fact p.Prime] (f : rootGeneratedRayGroup →* H) (hk : IsPGroup p f.ker)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (i : Omega) (t : ReflectingRootParameter)
    (he : f (distinguishedRootElement t)=f (distinguishedRootElement (.inl i))) : t=.inl i := by
  by_contra ht
  have hm : f (distinguishedRootElement t * distinguishedRootElement (.inl i))=1 := by
    rw [map_mul,he,← map_mul,distinguishedRootElement_mul_self,map_one]
  by_cases hz : hermitian (reflectingRootParameterVector t) (basicAxis i)=0
  · have ho := Atlas.Algebra.orderOf_map_prime_of_pgroup_kernel f hk (by decide : Nat.Prime 3)
      hp3 _ (distinguishedRootElement_zero_order t (.inl i) hz)
    rw [hm,orderOf_one] at ho
    norm_num at ho
  · have hx : orderOf (distinguishedRootElement t * distinguishedRootElement (.inl i))=2 := by
      rw [distinguishedRootElement_product_order _ _ ht]
      change (if hermitian (reflectingRootParameterVector t) (basicAxis i)=0 then 3 else 2)=2
      rw [if_neg hz]
    have ho := Atlas.Algebra.orderOf_map_prime_of_pgroup_kernel f hk (by decide : Nat.Prime 2)
      hp2 _ hx
    rw [hm,orderOf_one] at ho
    norm_num at ho

theorem basic_quotient_separation (p : ℕ) [Fact p.Prime] {H : Type*} [Group H]
    (f : rootGeneratedRayGroup →* H) (hk : IsPGroup p f.ker)
    (i : Omega) (t : ReflectingRootParameter)
    (he : f (distinguishedRootElement t)=f (distinguishedRootElement (.inl i))) : t=.inl i := by
  by_cases hp2 : p=2
  · subst p
    exact basic_quotient_separation_two f hk i t he
  by_cases hp3 : p=3
  · subst p
    exact basic_quotient_separation_three f hk i t he
  exact basic_quotient_separation_other p f hk hp2 hp3 i t he

/-- The source's separate two-, three-, and other-prime arguments exclude every
normal p-subgroup before any order, simplicity or frame-conjugacy theorem. -/
theorem rootGeneratedRay_normal_pgroup_eq_bot (p : ℕ) [Fact p.Prime]
    (N : Subgroup rootGeneratedRayGroup) [N.Normal] (hN : IsPGroup p N) : N=⊥ := by
  let f := QuotientGroup.mk' N
  have hk : IsPGroup p f.ker := by
    change IsPGroup p (QuotientGroup.mk' N).ker
    exact (QuotientGroup.ker_mk' N).symm ▸ hN
  let C : Subgroup rootGeneratedRayGroup := Subgroup.centralizer (N : Set rootGeneratedRayGroup)
  have hb (i : Omega) : distinguishedRootElement (.inl i) ∈ C := by
    intro n hn
    obtain ⟨t,ht⟩ := displayedRayOfParameter_surjective (n.val (displayedRayOfParameter (.inl i)))
    have hc := distinguishedRootElement_conjugation n (.inl i) t ht.symm
    have hfn : f n=1 := (QuotientGroup.eq_one_iff n).mpr hn
    have he : f (distinguishedRootElement t)=f (distinguishedRootElement (.inl i)) := by
      rw [← hc,map_mul,map_mul,map_inv,hfn,one_mul,inv_one,mul_one]
    have hti := basic_quotient_separation p f hk i t he
    rw [hti] at hc
    exact (mul_inv_eq_iff_eq_mul.mp hc)
  have hC : C=⊤ := by
    apply top_unique
    rw [← distinguishedRootClass_generates]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t,rfl⟩
    let i : Omega := Classical.arbitrary Omega
    obtain ⟨g,hg⟩ := rootGeneratedRayGroup_parameter_transitive (.inl i) t
    have he := distinguishedRootElement_conjugation g (.inl i) t hg
    rw [← he]
    exact (inferInstance : C.Normal).conj_mem _ (hb i) g
  have hle : N ≤ Subgroup.center rootGeneratedRayGroup :=
    Subgroup.centralizer_eq_top_iff_subset.mp hC
  rw [rootGeneratedRayGroup_center] at hle
  exact le_antisymm hle bot_le

end Atlas.Fischer
