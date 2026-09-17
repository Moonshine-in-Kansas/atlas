import Atlas.Conway.EisensteinBalancedNineProfile
import Atlas.Conway.EisensteinSignShell

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def eisensteinNineBridgeClass : EisensteinClasses :=
  eisensteinClassAction eisensteinNineBridgeIsometry
    (eisensteinClass (eisensteinTriadLatticeVector {0,1,7} eisensteinBalancedSourceBase_card 0))

def eisensteinNineProfileShell (p : EisensteinBalancedClassParameter) : EisensteinShell 6 :=
  (eisensteinNineProfileFiberEquiv p).val

theorem eisensteinNineProfileShell_injective : Function.Injective eisensteinNineProfileShell := by
  intro p q h
  exact eisensteinNineProfileFiberEquiv.injective (Subtype.ext h)

theorem eisensteinNineProfileShell_count (p : EisensteinBalancedClassParameter) (n : ℤ) :
    eisensteinNormCount (eisensteinNineProfileShell p) n=eisensteinNineProfileCount p n := by
  unfold eisensteinNormCount eisensteinNineProfileCount
  have h : (eisensteinNineProfileShell p).val.val=eisensteinNineProfileVector p :=
    eisensteinNineProfile_coordinates p
  rw [h]

def eisensteinNineClassVectors (c : EisensteinClasses) : Finset (EisensteinShell 6) :=
  Finset.univ.filter (fun x => eisensteinClass x.val=c ∧ eisensteinNormCount x 9=1)

theorem eisensteinNineProfile_image :
    (Finset.univ.filter (fun p : EisensteinBalancedClassParameter => eisensteinNineProfileCount p 9=1)).image
      eisensteinNineProfileShell=eisensteinNineClassVectors eisensteinNineBridgeClass := by
  ext x
  constructor
  · rintro hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,(eisensteinNineProfileFiberEquiv p).property,
      by rw [eisensteinNineProfileShell_count]; exact (Finset.mem_filter.mp hp).2⟩
  · intro hx
    have hh := (Finset.mem_filter.mp hx).2
    obtain ⟨p,hp⟩ := eisensteinNineProfileFiberEquiv.surjective ⟨x,hh.1⟩
    have he : eisensteinNineProfileShell p=x := congrArg Subtype.val hp
    apply Finset.mem_image.mpr
    refine ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,he⟩
    rw [← eisensteinNineProfileShell_count,he]
    exact hh.2

theorem eisensteinNineBridgeClass_nine_card :
    (eisensteinNineClassVectors eisensteinNineBridgeClass).card=18 := by
  rw [← eisensteinNineProfile_image,Finset.card_image_of_injective _ eisensteinNineProfileShell_injective]
  exact eisensteinNineProfile_counts.1

theorem eisensteinSignShell_involutive :
    Function.Involutive (eisensteinShellAction eisensteinSignIsometry 6) := by
  intro x
  apply Subtype.ext
  change eisensteinIntegralAction eisensteinSignIsometry
    (eisensteinIntegralAction eisensteinSignIsometry x.val)=x.val
  rw [eisensteinSignIntegral,eisensteinSignIntegral,neg_neg]

theorem eisensteinNineClassVectors_sign (c : EisensteinClasses) :
    (eisensteinNineClassVectors c).image (eisensteinShellAction eisensteinSignIsometry 6)=
      eisensteinNineClassVectors (-c) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    have hh := (Finset.mem_filter.mp hy).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,by rw [eisensteinSignShell_class,hh.1],
      by rw [eisensteinSignShell_normCount,hh.2]⟩
  · intro hx
    have hh := (Finset.mem_filter.mp hx).2
    refine Finset.mem_image.mpr ⟨eisensteinShellAction eisensteinSignIsometry 6 x,?_,
      eisensteinSignShell_involutive x⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,by rw [eisensteinSignShell_class,hh.1,neg_neg],
      by rw [eisensteinSignShell_normCount,hh.2]⟩

theorem eisensteinNineBridgeClass_neg_nine_card :
    (eisensteinNineClassVectors (-eisensteinNineBridgeClass)).card=18 := by
  rw [← eisensteinNineClassVectors_sign,Finset.card_image_of_injective _
    (eisensteinShellAction eisensteinSignIsometry 6).injective,eisensteinNineBridgeClass_nine_card]

theorem eisensteinNineBridgeFrame_nine_card :
    ((eisensteinFrameVectors eisensteinNineBridgeFrame).filter
      (fun x => eisensteinNormCount x 9=1)).card=36 := by
  have he : eisensteinNineBridgeFrame.val=eisensteinFramePair eisensteinNineBridgeClass := by
    rw [eisensteinNineBridgeFrame,eisensteinTriadFrame,eisensteinFrameAction_vector]
    rfl
  have hc : eisensteinNineBridgeClass ∈ eisensteinShellClasses 6 :=
    Finset.mem_image.mpr ⟨eisensteinNineProfileShell (0,0,0),Finset.mem_univ _,
      (eisensteinNineProfileFiberEquiv (0,0,0)).property⟩
  have hn : eisensteinNineBridgeClass≠ -eisensteinNineBridgeClass :=
    Ne.symm (eisensteinClasses_neg_ne (fun h =>
      eisensteinShellClasses_zero_not_mem 6 (by decide) (h ▸ hc)))
  have hd : Disjoint (eisensteinNineClassVectors eisensteinNineBridgeClass)
      (eisensteinNineClassVectors (-eisensteinNineBridgeClass)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hn ((Finset.mem_filter.mp hx).2.1.symm.trans (Finset.mem_filter.mp hy).2.1)
  have hf : (eisensteinFrameVectors eisensteinNineBridgeFrame).filter
      (fun x => eisensteinNormCount x 9=1)=
      eisensteinNineClassVectors eisensteinNineBridgeClass ∪
        eisensteinNineClassVectors (-eisensteinNineBridgeClass) := by
    ext x
    simp [eisensteinFrameVectors,eisensteinNineClassVectors,he,eisensteinFramePair,or_and_right]
  rw [hf,Finset.card_union_of_disjoint hd,eisensteinNineBridgeClass_nine_card,
    eisensteinNineBridgeClass_neg_nine_card]

theorem eisensteinLocal_frame_normCount_card (g : eisensteinCoordinateFrameStabilizer)
    (F : EisensteinFrame) (n : ℤ) (k : ℕ) :
    ((eisensteinFrameVectors (g • F)).filter (fun x => eisensteinNormCount x n=k)).card=
      ((eisensteinFrameVectors F).filter (fun x => eisensteinNormCount x n=k)).card := by
  change ((eisensteinFrameVectors (g.val • F)).filter _).card=_
  rw [eisensteinFrameAction_vectors,Finset.filter_image]
  simp_rw [eisensteinLocalNormCount]
  rw [Finset.card_image_of_injective _ (eisensteinShellAction g.val 6).injective]

theorem eisensteinNineBridgeOrbit_nine_card (F : EisensteinFrame)
    (hF : F ∈ MulAction.orbit eisensteinCoordinateFrameStabilizer eisensteinNineBridgeFrame) :
    ((eisensteinFrameVectors F).filter (fun x => eisensteinNormCount x 9=1)).card=36 := by
  obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hF
  rw [eisensteinLocal_frame_normCount_card,eisensteinNineBridgeFrame_nine_card]

end Atlas.Conway
