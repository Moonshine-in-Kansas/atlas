import Atlas.Conway.EisensteinBalancedNineProfileParameters
import Atlas.Conway.EisensteinBalancedNineFamily
import Atlas.Conway.EisensteinNineFrameFiber
import Atlas.Lattices.EisensteinFrameVectorMembership
import Atlas.Lattices.EisensteinBalancedNineCoordinateCounts

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem eisensteinNineProfileShell_eq_raw (p : EisensteinBalancedClassParameter)
    (hp : eisensteinNineProfileCount p 9=1) :
    eisensteinNineProfileShell p=eisensteinBalancedNineParameterShell (eisensteinNineProfileRawParameter p) := by
  apply Subtype.ext
  apply Subtype.ext
  exact (eisensteinNineProfile_coordinates p).trans (eisensteinNineProfileRaw_correct p hp).symm

theorem eisensteinNineBridgeClass_raw (x : EisensteinShell 6)
    (hx : x ∈ eisensteinNineClassVectors eisensteinNineBridgeClass) :
    ∃ p : EisensteinBalancedNineParameters,eisensteinBalancedNineParameterShell p=x := by
  rw [← eisensteinNineProfile_image] at hx
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  exact ⟨eisensteinNineProfileRawParameter p,
    (eisensteinNineProfileShell_eq_raw p (Finset.mem_filter.mp hp).2).symm⟩

theorem eisensteinNineBridgeFrame_raw (x : EisensteinShell 6)
    (hx : x ∈ eisensteinFrameVectors eisensteinNineBridgeFrame)
    (hn : eisensteinNormCount x 9=1) :
    ∃ p : EisensteinBalancedNineParameters,eisensteinBalancedNineParameterShell p=x := by
  have he : eisensteinNineBridgeFrame.val=eisensteinFramePair eisensteinNineBridgeClass := by
    rw [eisensteinNineBridgeFrame,eisensteinTriadFrame,eisensteinFrameAction_vector]
    rfl
  have hc : eisensteinClass x.val=eisensteinNineBridgeClass ∨
      eisensteinClass x.val= -eisensteinNineBridgeClass := by
    have h := (Finset.mem_filter.mp hx).2
    rw [he] at h
    simpa [eisensteinFramePair] using h
  rcases hc with hc|hc
  · exact eisensteinNineBridgeClass_raw x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,hn⟩)
  · let y := eisensteinShellAction eisensteinSignIsometry 6 x
    have hy : y ∈ eisensteinNineClassVectors eisensteinNineBridgeClass := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
      · rw [eisensteinSignShell_class,hc,neg_neg]
      · rw [eisensteinSignShell_normCount,hn]
    obtain ⟨p,hp⟩ := eisensteinNineBridgeClass_raw y hy
    refine ⟨eisensteinBalancedNineNegParameter p,?_⟩
    have he := congrArg (eisensteinShellAction eisensteinSignIsometry 6) hp
    rw [eisensteinSignShell_involutive] at he
    apply Subtype.ext
    change eisensteinBalancedNineParameterLatticeVector (eisensteinBalancedNineNegParameter p)=x.val
    rw [eisensteinBalancedNineNegParameter_vector,← eisensteinSignIntegral]
    exact congrArg Subtype.val he

theorem eisensteinNineBridgeFrame_mem_family : eisensteinNineBridgeFrame ∈ eisensteinBalancedNineFamily := by
  have hp : 0 < ((eisensteinFrameVectors eisensteinNineBridgeFrame).filter
      (fun x => eisensteinNormCount x 9=1)).card := by rw [eisensteinNineBridgeFrame_nine_card]; decide
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hp
  have h := Finset.mem_filter.mp hx
  obtain ⟨p,rfl⟩ := eisensteinNineBridgeFrame_raw x h.1 h.2
  refine Finset.mem_image.mpr ⟨p,Finset.mem_univ _,?_⟩
  exact (eisensteinFrameOfVector_eq_iff_mem _ _).mpr h.1

def EisensteinBalancedNineFrameFiber (F : EisensteinFrame) :=
  {p : EisensteinBalancedNineParameters // eisensteinBalancedNineParameterFrame p=F}

def eisensteinNineBridgeFrameFiberEquiv : EisensteinBalancedNineFrameFiber eisensteinNineBridgeFrame ≃
    {x : EisensteinShell 6 // x ∈ eisensteinFrameVectors eisensteinNineBridgeFrame ∧ eisensteinNormCount x 9=1} :=
  Equiv.ofBijective (fun p => ⟨eisensteinBalancedNineParameterShell p.val,
    (eisensteinFrameOfVector_eq_iff_mem _ _).mp p.prop,
    eisensteinBalancedNineParameter_normCount9 p.val⟩) (by
      constructor
      · intro p q h
        apply Subtype.ext
        exact eisensteinBalancedNineParameterShell_injective (congrArg Subtype.val h)
      · intro x
        obtain ⟨p,hp⟩ := eisensteinNineBridgeFrame_raw x.val x.prop.1 x.prop.2
        refine ⟨⟨p,?_⟩,Subtype.ext hp⟩
        apply (eisensteinFrameOfVector_eq_iff_mem _ _).mpr
        rw [hp]
        exact x.prop.1)

theorem eisensteinNineBridgeFrameFiber_card :
    Nat.card (EisensteinBalancedNineFrameFiber eisensteinNineBridgeFrame)=36 := by
  rw [Nat.card_congr eisensteinNineBridgeFrameFiberEquiv,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have he : Finset.univ.filter (fun x : EisensteinShell 6 =>
      x ∈ eisensteinFrameVectors eisensteinNineBridgeFrame ∧ eisensteinNormCount x 9=1) =
      (eisensteinFrameVectors eisensteinNineBridgeFrame).filter (fun x => eisensteinNormCount x 9=1) := by
    ext x
    simp
  rw [he,eisensteinNineBridgeFrame_nine_card]

end Atlas.Conway
