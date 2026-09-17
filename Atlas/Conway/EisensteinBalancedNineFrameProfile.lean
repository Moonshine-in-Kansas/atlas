import Atlas.Conway.EisensteinBalancedNineLocalFiber
import Atlas.Conway.EisensteinSignShell

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

def EisensteinBalancedNineVectorPattern (x : EisensteinShell 6) : Prop :=
  (eisensteinNormCount x 0=5 ∧ eisensteinNormCount x 3=6 ∧ eisensteinNormCount x 9=1) ∨
    (eisensteinNormCount x 0=3 ∧ eisensteinNormCount x 3=9)

theorem eisensteinNineProfile_actual_pattern
    (x : EisensteinClassFiber 6 (eisensteinClassAction eisensteinNineBridgeIsometry
      (eisensteinClass (eisensteinTriadLatticeVector {0,1,7} eisensteinBalancedSourceBase_card 0)))) :
    EisensteinBalancedNineVectorPattern x.val := by
  obtain ⟨p,hp⟩ := eisensteinNineProfile_exhaustion x
  have hc (n : ℤ) : eisensteinNormCount x.val n=eisensteinNineProfileCount p n := by
    unfold eisensteinNormCount eisensteinNineProfileCount
    rw [hp]
  simpa only [EisensteinBalancedNineVectorPattern,hc] using eisensteinNineProfile_patterns p

theorem eisensteinNineSourceFrame_pattern (x : EisensteinShell 6)
    (hx : x ∈ eisensteinFrameVectors (eisensteinNineBridgeIsometry •
      eisensteinTriadFrame {0,1,7} eisensteinBalancedSourceBase_card 0)) :
    EisensteinBalancedNineVectorPattern x := by
  classical
  let c := eisensteinClassAction eisensteinNineBridgeIsometry
    (eisensteinClass (eisensteinTriadLatticeVector {0,1,7} eisensteinBalancedSourceBase_card 0))
  have he : (eisensteinNineBridgeIsometry • eisensteinTriadFrame {0,1,7}
      eisensteinBalancedSourceBase_card 0).val=eisensteinFramePair c := by
    rw [eisensteinTriadFrame,eisensteinFrameAction_vector]
    rfl
  have hc : eisensteinClass x.val=c ∨ eisensteinClass x.val= -c := by
    have hh := (Finset.mem_filter.mp hx).2
    rw [he] at hh
    simpa [eisensteinFramePair] using hh
  rcases hc with hc|hc
  · exact eisensteinNineProfile_actual_pattern ⟨x,hc⟩
  · let y := eisensteinShellAction eisensteinSignIsometry 6 x
    have hy : eisensteinClass y.val=c := by
      rw [eisensteinSignShell_class,hc,neg_neg]
    have h := eisensteinNineProfile_actual_pattern ⟨y,hy⟩
    simpa only [EisensteinBalancedNineVectorPattern,y,eisensteinSignShell_normCount] using h

/-- Every vector of every balanced norm-nine frame has one of the two specified profiles. -/
theorem eisensteinBalancedNineFrame_pattern (F : EisensteinFrame) (hF : F ∈ eisensteinBalancedNineFamily)
    (x : EisensteinShell 6) (hx : x ∈ eisensteinFrameVectors F) :
    EisensteinBalancedNineVectorPattern x := by
  classical
  let F0 := eisensteinNineBridgeIsometry •
    eisensteinTriadFrame {0,1,7} eisensteinBalancedSourceBase_card 0
  have hF0 : F0 ∈ eisensteinBalancedNineFamily := eisensteinNineBridgeFrame_mem_family
  obtain ⟨g,hg⟩ := eisensteinBalancedNineFamily_transitive F0 F hF0 hF
  rw [← hg,eisensteinFrameAction_vectors] at hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have h := eisensteinNineSourceFrame_pattern y hy
  simpa only [EisensteinBalancedNineVectorPattern,eisensteinLocalNormCount] using h

end Atlas.Conway
