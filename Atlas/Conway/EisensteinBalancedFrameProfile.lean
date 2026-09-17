import Atlas.Conway.EisensteinBalancedClassExhaustion
import Atlas.Conway.EisensteinSignShell

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

def EisensteinBalancedVectorPattern (x : EisensteinShell 6) : Prop :=
  (eisensteinNormCount x 0=6 ∧ eisensteinNormCount x 3=5 ∧ eisensteinNormCount x 12=1) ∨
    (eisensteinNormCount x 0=3 ∧ eisensteinNormCount x 3=9)

theorem eisensteinBalancedProfile_actual_pattern
    (x : EisensteinClassFiber 6 (eisensteinClassAction eisensteinFourierIsometry
      (eisensteinClass (eisensteinTriadLatticeVector {0,1,7} eisensteinBalancedSourceBase_card 0)))) :
    EisensteinBalancedVectorPattern x.val := by
  obtain ⟨p,hp⟩ := eisensteinBalancedProfile_exhaustion x
  have hc (n : ℤ) : eisensteinNormCount x.val n=eisensteinBalancedProfileCount p n := by
    unfold eisensteinNormCount eisensteinBalancedProfileCount
    rw [hp]
  simpa only [EisensteinBalancedVectorPattern,hc] using eisensteinBalancedProfile_patterns p

theorem eisensteinBalancedSourceFrame_pattern (x : EisensteinShell 6)
    (hx : x ∈ eisensteinFrameVectors (eisensteinFourierIsometry •
      eisensteinTriadFrame {0,1,7} eisensteinBalancedSourceBase_card 0)) :
    EisensteinBalancedVectorPattern x := by
  classical
  let c := eisensteinClassAction eisensteinFourierIsometry
    (eisensteinClass (eisensteinTriadLatticeVector {0,1,7} eisensteinBalancedSourceBase_card 0))
  have he : (eisensteinFourierIsometry • eisensteinTriadFrame {0,1,7}
      eisensteinBalancedSourceBase_card 0).val=eisensteinFramePair c := by
    rw [eisensteinTriadFrame,eisensteinFrameAction_vector]
    rfl
  have hc : eisensteinClass x.val=c ∨ eisensteinClass x.val= -c := by
    have hh := (Finset.mem_filter.mp hx).2
    rw [he] at hh
    simpa [eisensteinFramePair] using hh
  rcases hc with hc|hc
  · exact eisensteinBalancedProfile_actual_pattern ⟨x,hc⟩
  · let y := eisensteinShellAction eisensteinSignIsometry 6 x
    have hy : eisensteinClass y.val=c := by
      rw [eisensteinSignShell_class,hc,neg_neg]
    have h := eisensteinBalancedProfile_actual_pattern ⟨y,hy⟩
    simpa only [EisensteinBalancedVectorPattern,y,eisensteinSignShell_normCount] using h

/-- Every vector of every balanced-heavy frame has one of the two specified profiles. -/
theorem eisensteinBalancedFrame_pattern (F : EisensteinFrame) (hF : F ∈ eisensteinBalancedFamily)
    (x : EisensteinShell 6) (hx : x ∈ eisensteinFrameVectors F) :
    EisensteinBalancedVectorPattern x := by
  classical
  let F0 := eisensteinFourierIsometry •
    eisensteinTriadFrame {0,1,7} eisensteinBalancedSourceBase_card 0
  have hF0 : F0 ∈ eisensteinBalancedFamily := eisensteinFourier_triad_mem_balanced
  obtain ⟨g,hg⟩ := eisensteinBalancedFamily_transitive F0 F hF0 hF
  rw [← hg,eisensteinFrameAction_vectors] at hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have h := eisensteinBalancedSourceFrame_pattern y hy
  simpa only [EisensteinBalancedVectorPattern,eisensteinLocalNormCount] using h

end Atlas.Conway
