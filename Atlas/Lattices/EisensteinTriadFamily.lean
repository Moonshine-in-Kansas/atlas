import Atlas.Lattices.EisensteinTriadClassCriteria

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev EisensteinTriadSupport := ↥ternaryTriads
abbrev EisensteinTriadParameter := EisensteinTriadSupport × ZMod 3

theorem eisensteinTriadSupport_card (s : EisensteinTriadSupport) : s.val.card=3 :=
  (Finset.mem_powersetCard.mp s.prop).2

def eisensteinTriadParameterWord (p : EisensteinTriadParameter) : TernaryWord :=
  Pi.single (p.1.val.orderEmbOfFin (eisensteinTriadSupport_card p.1) 0) p.2

theorem eisensteinTriadParameterWord_sum (p : EisensteinTriadParameter) :
    ∑ i ∈ p.1.val,eisensteinTriadParameterWord p i = p.2 := by
  simp [eisensteinTriadParameterWord,Pi.single_apply,Finset.orderEmbOfFin_mem]

def eisensteinTriadParameterFrame (p : EisensteinTriadParameter) : EisensteinFrame :=
  eisensteinTriadFrame p.1.val (eisensteinTriadSupport_card p.1) (eisensteinTriadParameterWord p)

theorem eisensteinTriadParameterFrame_eq_iff (p q : EisensteinTriadParameter) :
    eisensteinTriadParameterFrame p = eisensteinTriadParameterFrame q ↔
      (ternaryTriadWord p.1.val-ternaryTriadWord q.1.val ∈ ternaryGolay ∧ p.2=q.2) ∨
      (ternaryTriadWord p.1.val+ternaryTriadWord q.1.val ∈ ternaryGolay ∧ p.2+q.2=0) := by
  unfold eisensteinTriadParameterFrame
  rw [eisensteinTriadFrame_eq_iff,eisensteinTriadParameterWord_sum,eisensteinTriadParameterWord_sum]

theorem eisensteinTriadParameterFrame_same_support (s : EisensteinTriadSupport) (a b : ZMod 3) :
    eisensteinTriadParameterFrame (s,a) = eisensteinTriadParameterFrame (s,b) ↔ a=b := by
  rw [eisensteinTriadParameterFrame_eq_iff]
  have hn : ternaryTriadWord s.val+ternaryTriadWord s.val ∉ ternaryGolay :=
    ternaryTriad_sign_unique s.val s.val (eisensteinTriadSupport_card s)
      (by simpa using ternaryGolay.zero_mem)
  simp [hn]

theorem eisensteinTriadParameter_count : Nat.card EisensteinTriadParameter = 660 := by
  rw [Nat.card_prod]
  have hs : Nat.card EisensteinTriadSupport=220 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,ternaryTriads_card]
  rw [hs]
  norm_num

def eisensteinTriadFamily : Finset EisensteinFrame :=
  Finset.univ.image eisensteinTriadParameterFrame

theorem eisensteinTriadParameterFrame_related (p q : EisensteinTriadParameter)
    (h : eisensteinTriadParameterFrame p = eisensteinTriadParameterFrame q) :
    q.1.val ∈ ternaryTriadPartners p.1.val := by
  apply Finset.mem_filter.mpr
  refine ⟨q.1.prop,(ternaryTriadRelated_iff _ _).mpr ?_⟩
  rcases (eisensteinTriadParameterFrame_eq_iff p q).mp h with h | h
  · exact ⟨true,by simpa using h.1⟩
  · exact ⟨false,by simpa using h.1⟩

theorem eisensteinTriadParameterFrame_exists_partner (p : EisensteinTriadParameter)
    (t : Finset (Fin 12)) (ht : t ∈ ternaryTriadPartners p.1.val) :
    ∃ q : EisensteinTriadParameter, q.1.val=t ∧
      eisensteinTriadParameterFrame p=eisensteinTriadParameterFrame q := by
  obtain ⟨ht,hrel⟩ := Finset.mem_filter.mp ht
  obtain ⟨b,hb⟩ := (ternaryTriadRelated_iff _ _).mp hrel
  cases b
  · refine ⟨(⟨t,ht⟩,-p.2),rfl,(eisensteinTriadParameterFrame_eq_iff _ _).mpr ?_⟩
    exact Or.inr ⟨by simpa using hb,add_neg_cancel _⟩
  · refine ⟨(⟨t,ht⟩,p.2),rfl,(eisensteinTriadParameterFrame_eq_iff _ _).mpr ?_⟩
    exact Or.inl ⟨by simpa using hb,rfl⟩

def eisensteinTriadFiberMap (p : EisensteinTriadParameter) :
    {q : EisensteinTriadParameter // eisensteinTriadParameterFrame q=eisensteinTriadParameterFrame p} →
      ↥(ternaryTriadPartners p.1.val) := fun q =>
  ⟨q.val.1.val,eisensteinTriadParameterFrame_related p q.val q.prop.symm⟩

theorem eisensteinTriadFiberMap_bijective (p : EisensteinTriadParameter) :
    Function.Bijective (eisensteinTriadFiberMap p) := by
  constructor
  · rintro ⟨⟨s,a⟩,ha⟩ ⟨⟨t,b⟩,hb⟩ he
    have hv := congrArg (fun z : ↥(ternaryTriadPartners p.1.val) => z.val) he
    have hst : s=t := Subtype.ext hv
    subst t
    have hab := (eisensteinTriadParameterFrame_same_support s a b).mp (ha.trans hb.symm)
    subst b
    rfl
  · rintro ⟨t,ht⟩
    obtain ⟨q,hq,he⟩ := eisensteinTriadParameterFrame_exists_partner p t ht
    exact ⟨⟨q,he.symm⟩,Subtype.ext hq⟩

theorem eisensteinTriadParameterFrame_fiber_card (p : EisensteinTriadParameter) :
    Nat.card {q : EisensteinTriadParameter //
      eisensteinTriadParameterFrame q=eisensteinTriadParameterFrame p} = 4 := by
  rw [Nat.card_congr (Equiv.ofBijective _ (eisensteinTriadFiberMap_bijective p)),
    Nat.card_eq_fintype_card,Fintype.card_coe,
    ternaryTriadPartners_card _ (eisensteinTriadSupport_card p.1)]

theorem eisensteinTriadFamily_card : eisensteinTriadFamily.card=165 := by
  have h := Finset.card_eq_sum_card_image (f := eisensteinTriadParameterFrame) Finset.univ
  have hf (F : EisensteinFrame) (hF : F ∈ eisensteinTriadFamily) :
      (Finset.univ.filter (fun q => eisensteinTriadParameterFrame q=F)).card=4 := by
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hF
    rw [← Fintype.card_subtype,← Nat.card_eq_fintype_card]
    exact eisensteinTriadParameterFrame_fiber_card p
  change Fintype.card EisensteinTriadParameter =
    ∑ F ∈ eisensteinTriadFamily,(Finset.univ.filter (fun q => eisensteinTriadParameterFrame q=F)).card at h
  rw [← Nat.card_eq_fintype_card,eisensteinTriadParameter_count] at h
  have hh : (∑ F ∈ eisensteinTriadFamily,
      (Finset.univ.filter (fun q => eisensteinTriadParameterFrame q=F)).card) =
      eisensteinTriadFamily.card*4 := by
    simp_rw [Finset.sum_congr rfl hf]
    simp
  rw [hh] at h
  omega

theorem eisensteinTriadFrame_mem_family (s : Finset (Fin 12)) (hs : s.card=3)
    (a : TernaryWord) : eisensteinTriadFrame s hs a ∈ eisensteinTriadFamily := by
  let p : EisensteinTriadParameter :=
    (⟨s,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hs⟩⟩,∑ i ∈ s,a i)
  refine Finset.mem_image.mpr ⟨p,Finset.mem_univ _,?_⟩
  apply eisensteinTriadFrame_eq_of_sum
  exact eisensteinTriadParameterWord_sum p

end Atlas.Lattices
