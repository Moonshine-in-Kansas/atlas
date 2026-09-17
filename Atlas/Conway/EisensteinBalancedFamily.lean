import Atlas.Conway.EisensteinBalancedNegation

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def eisensteinBalancedClassFrame (c : ↥eisensteinBalancedClasses) : EisensteinFrame :=
  ⟨eisensteinFramePair c.val,by
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp c.prop
    rw [← hp]
    exact (eisensteinFrameOfVector (eisensteinBalancedPhasedShellVector p.1 p.2.1 p.2.2)).prop⟩

def eisensteinBalancedFamily : Finset EisensteinFrame :=
  Finset.univ.image eisensteinBalancedClassFrame

def eisensteinBalancedClassNeg (c : ↥eisensteinBalancedClasses) : ↥eisensteinBalancedClasses :=
  ⟨-c.val,eisensteinBalancedClasses_neg c.val c.prop⟩

theorem eisensteinBalancedClassNeg_ne (c : ↥eisensteinBalancedClasses) :
    eisensteinBalancedClassNeg c≠c := by
  intro h
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp c.prop
  have hn : c.val≠0 := hp ▸ eisensteinBalancedParameterClass_nonzero p
  exact eisensteinClasses_neg_ne hn (congrArg Subtype.val h)

theorem eisensteinBalancedClassFrame_fiber (c d : ↥eisensteinBalancedClasses) :
    eisensteinBalancedClassFrame d=eisensteinBalancedClassFrame c ↔
      d=c ∨ d=eisensteinBalancedClassNeg c := by
  rw [Subtype.ext_iff]
  change eisensteinFramePair d.val=eisensteinFramePair c.val ↔ _
  rw [eisensteinFramePair_eq_iff]
  constructor
  · rintro (h|h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl|rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem eisensteinBalancedClassFrame_fiber_card (c : ↥eisensteinBalancedClasses) :
    Nat.card {d : ↥eisensteinBalancedClasses //
      eisensteinBalancedClassFrame d=eisensteinBalancedClassFrame c}=2 := by
  let e : {d : ↥eisensteinBalancedClasses //
      eisensteinBalancedClassFrame d=eisensteinBalancedClassFrame c} ≃
      ({c,eisensteinBalancedClassNeg c} : Finset ↥eisensteinBalancedClasses) :=
    Equiv.subtypeEquivRight (fun d => by rw [eisensteinBalancedClassFrame_fiber]; simp)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe,
    Finset.card_pair (eisensteinBalancedClassNeg_ne c).symm]

/-- Symbolic count: 220 balanced words, six heavy positions and243 phases,
divided by nine for an oriented class and by two for opposite classes. -/
theorem eisensteinBalancedFamily_card : eisensteinBalancedFamily.card=17820 := by
  have h := Finset.card_eq_sum_card_image (f := eisensteinBalancedClassFrame) Finset.univ
  have hf (F : EisensteinFrame) (hF : F ∈ eisensteinBalancedFamily) :
      (Finset.univ.filter (fun c => eisensteinBalancedClassFrame c=F)).card=2 := by
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hF
    rw [← Fintype.card_subtype,← Nat.card_eq_fintype_card]
    exact eisensteinBalancedClassFrame_fiber_card c
  change Fintype.card ↥eisensteinBalancedClasses =
    ∑ F ∈ eisensteinBalancedFamily,(Finset.univ.filter (fun c => eisensteinBalancedClassFrame c=F)).card at h
  rw [Fintype.card_coe,eisensteinBalancedClasses_card] at h
  have hh : (∑ F ∈ eisensteinBalancedFamily,
      (Finset.univ.filter (fun c => eisensteinBalancedClassFrame c=F)).card)=
        eisensteinBalancedFamily.card*2 := by
    simp_rw [Finset.sum_congr rfl hf]
    simp
  rw [hh] at h
  omega

def eisensteinBalancedParameterFrame (p : EisensteinBalancedParameters) : EisensteinFrame :=
  eisensteinFrameOfVector (eisensteinBalancedPhasedShellVector p.1 p.2.1 p.2.2)

theorem eisensteinBalancedParameterFrame_mem (p : EisensteinBalancedParameters) :
    eisensteinBalancedParameterFrame p ∈ eisensteinBalancedFamily := by
  refine Finset.mem_image.mpr
    ⟨⟨eisensteinBalancedParameterClass p,Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩⟩,
      Finset.mem_univ _,?_⟩
  rfl

theorem eisensteinBalancedFamily_mem_iff (F : EisensteinFrame) :
    F ∈ eisensteinBalancedFamily ↔ ∃ p : EisensteinBalancedParameters,
      eisensteinBalancedParameterFrame p=F := by
  constructor
  · intro hF
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp c.prop
    exact ⟨p,Subtype.ext (congrArg eisensteinFramePair hp)⟩
  · rintro ⟨p,rfl⟩
    exact eisensteinBalancedParameterFrame_mem p

end Atlas.Conway
