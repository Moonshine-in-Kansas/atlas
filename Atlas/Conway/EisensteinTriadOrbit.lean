import Atlas.Lattices.EisensteinTriadFamily
import Atlas.Conway.EisensteinFrameAction
import Atlas.Conway.EisensteinFrameOrder
import Atlas.Conway.EisensteinFourier
import Atlas.Conway.EisensteinStandardFrame

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

theorem eisensteinTriadFrame_monomial (s : Finset (Fin 12)) (hs : s.card=3)
    (a : TernaryWord) (t : ternaryGolay) (g : TernaryPureAutomorphism) :
    (eisensteinMonomialParameterIsometry (false,t,g)) • eisensteinTriadFrame s hs a =
      eisensteinTriadFrame (s.map g.val.toEmbedding) (by simpa using hs)
        (t.val+(fun i => a (g.val.symm i))) := by
  rw [eisensteinTriadFrame,eisensteinFrameAction_vector]
  apply congrArg eisensteinFrameOfVector
  apply Subtype.ext
  apply Subtype.ext
  apply eisensteinCoordinateEmbedding_injective
  change eisensteinCoordinateEmbedding
    (eisensteinIntegralAction (eisensteinMonomialParameterIsometry (false,t,g))
      (eisensteinTriadLatticeVector s hs a)).val = _
  rw [eisensteinIntegralAction_agrees]
  funext i
  rw [eisensteinMonomialParameterIsometry_apply]
  change eisensteinToRational (eisensteinSignedPhase false (t.val i)) *
    eisensteinToRational (eisensteinTriadVector s a (g.val.symm i)) =
      eisensteinToRational (eisensteinTriadVector (s.map g.val.toEmbedding)
        (t.val+(fun i => a (g.val.symm i))) i)
  by_cases hi : g.val.symm i ∈ s
  · simp [eisensteinSignedPhase,eisensteinTriadVector,Finset.mem_map_equiv,hi,
      eisensteinPhase_add,map_mul]
    ring
  · simp [eisensteinSignedPhase,eisensteinTriadVector,Finset.mem_map_equiv,hi]

set_option maxRecDepth 10000 in
/-- The full standard-frame stabilizer is transitive on the intrinsic triad family. -/
theorem eisensteinTriadFamily_transitive (F G : EisensteinFrame)
    (hF : F ∈ eisensteinTriadFamily) (hG : G ∈ eisensteinTriadFamily) :
    ∃ g : eisensteinCoordinateFrameStabilizer, g.val • F=G := by
  classical
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hF
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hG
  obtain ⟨g,hg⟩ := ternaryTriads_transitive p.1.val q.1.val
    (eisensteinTriadSupport_card p.1) (eisensteinTriadSupport_card q.1)
  let a : TernaryWord := fun i => eisensteinTriadParameterWord p (g.val.symm i)
  obtain ⟨t,ht⟩ := ternaryTriad_sum_surjective q.1.val (eisensteinTriadSupport_card q.1)
    (q.2-∑ i ∈ q.1.val,a i)
  refine ⟨eisensteinFrameFromParameters (false,t,g),?_⟩
  change eisensteinMonomialParameterIsometry (false,t,g) •
    eisensteinTriadFrame p.1.val _ (eisensteinTriadParameterWord p) = _
  rw [eisensteinTriadFrame_monomial]
  change eisensteinTriadFrame (p.1.val.map g.val.toEmbedding) _ (t.val+a) = _
  have hh : eisensteinTriadFrame q.1.val (eisensteinTriadSupport_card q.1) (t.val+a) =
      eisensteinTriadParameterFrame q := by
    apply eisensteinTriadFrame_eq_of_sum
    rw [eisensteinTriadParameterWord_sum]
    simp only [Pi.add_apply,Finset.sum_add_distrib,ht,sub_add_cancel]
  convert hh using 1 <;> congr 1

/-- The corrected Fourier word joins the standard frame to the triad family. -/
theorem eisensteinFourier_standard_triad :
    eisensteinFourierIsometry • eisensteinStandardFrame =
      eisensteinTriadFrame ternaryBaseTriad (by decide) 0 := by
  have hv : eisensteinIntegralAction eisensteinFourierIsometry
      (eisensteinIntegralFrameVector (0,1)) =
      -eisensteinTriadLatticeVector ternaryBaseTriad (by decide) 0 := by
    apply Subtype.ext
    apply eisensteinCoordinateEmbedding_injective
    rw [eisensteinIntegralAction_agrees]
    change eisensteinFourier _ = _
    rw [eisensteinFourier_apply]
    decide +kernel
  rw [eisensteinStandardFrame,eisensteinFrameAction_vector]
  apply Subtype.ext
  change eisensteinFramePair (eisensteinClass (eisensteinIntegralAction eisensteinFourierIsometry
    (eisensteinIntegralFrameVector (0,1)))) =
      eisensteinFramePair (eisensteinClass (eisensteinTriadLatticeVector ternaryBaseTriad (by decide) 0))
  rw [hv,map_neg,eisensteinFramePair_neg]

theorem eisensteinFourier_standard_mem_triad :
    eisensteinFourierIsometry • eisensteinStandardFrame ∈ eisensteinTriadFamily := by
  classical
  rw [eisensteinFourier_standard_triad]
  let p : EisensteinTriadParameter := (⟨ternaryBaseTriad,by decide⟩,0)
  refine Finset.mem_image.mpr ⟨p,Finset.mem_univ _,?_⟩
  unfold eisensteinTriadParameterFrame
  have he : eisensteinTriadParameterWord p = 0 := by
    simp [eisensteinTriadParameterWord,p]
  rw [he]

theorem eisensteinSign_frame (F : EisensteinFrame) : eisensteinSignIsometry • F=F := by
  classical
  obtain ⟨c,hc,he⟩ := eisensteinFrame_pair F
  obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hc
  have hF : F=eisensteinFrameOfVector x := by
    apply Subtype.ext
    change F.val=eisensteinFramePair (eisensteinClass x.val)
    rw [hx]
    exact he
  rw [hF,eisensteinFrameAction_vector]
  have hv : eisensteinIntegralAction eisensteinSignIsometry x.val = -x.val := by
    apply Subtype.ext
    apply eisensteinCoordinateEmbedding_injective
    rw [eisensteinIntegralAction_agrees]
    change -eisensteinCoordinateEmbedding x.val.val = eisensteinCoordinateEmbedding (-x.val.val)
    rw [map_neg]
  apply Subtype.ext
  change eisensteinFramePair (eisensteinClass (eisensteinIntegralAction eisensteinSignIsometry x.val)) =
    eisensteinFramePair (eisensteinClass x.val)
  rw [hv,map_neg,eisensteinFramePair_neg]

theorem eisensteinTriadFamily_invariant (g : eisensteinCoordinateFrameStabilizer)
    (F : EisensteinFrame) (hF : F ∈ eisensteinTriadFamily) :
    g.val • F ∈ eisensteinTriadFamily := by
  classical
  obtain ⟨p,rfl⟩ := eisensteinFrameFromParameters_surjective g
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hF
  rcases p with ⟨b,t,g⟩
  have hm : eisensteinMonomialParameterIsometry (false,t,g) • eisensteinTriadParameterFrame q ∈
      eisensteinTriadFamily := by
    rw [eisensteinTriadParameterFrame,eisensteinTriadFrame_monomial]
    exact eisensteinTriadFrame_mem_family _ _ _
  cases b
  · exact hm
  · change eisensteinMonomialParameterIsometry (true,t,g) • eisensteinTriadParameterFrame q ∈ _
    have he : eisensteinMonomialParameterIsometry (true,t,g) =
        eisensteinSignIsometry*eisensteinMonomialParameterIsometry (false,t,g) := by
      simp [eisensteinMonomialParameterIsometry,mul_assoc]
    rw [he,mul_smul,eisensteinSign_frame]
    exact hm

/-- The first nontrivial suborbit is exactly the 165 intrinsic triad frames. -/
theorem eisensteinTriadFamily_orbit (F : EisensteinFrame) (hF : F ∈ eisensteinTriadFamily) :
    MulAction.orbit eisensteinCoordinateFrameStabilizer F = (eisensteinTriadFamily : Set EisensteinFrame) := by
  ext G
  constructor
  · rintro ⟨g,rfl⟩
    exact eisensteinTriadFamily_invariant g F hF
  · intro hG
    obtain ⟨g,hg⟩ := eisensteinTriadFamily_transitive F G hF hG
    exact ⟨g,hg⟩

end Atlas.Conway
