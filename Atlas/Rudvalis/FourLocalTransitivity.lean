import Atlas.Rudvalis.FourLocalLabels

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

/-- Every four-block minimum avoiding the fixed coordinate row lies in the actual stabilizer orbit. -/
theorem fourLocal_minimum_word_orbit (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (h16 : euclideanWeight w=16) (hf : admissibleFourSupport (reduce w))
    (hzero : ∀x : E,reduce w (rowLabel 0,x)=0) :
    ∃g : FourLocalStabilizer,monomialHom g.val.val (quaternarySeed (3,0,0,0))=w := by
  obtain ⟨a,ε,hr,hε,hs⟩ := hf
  have ha : dot a.val (rowLabel 0).val=0 := by
    have hp := fourNormal_pair ε a.val (rowLabel 0) 0
    rw [←hr,hzero,hzero,zero_add] at hp
    exact hp.symm
  obtain ⟨n,hn⟩ := codeT_label_cycle a ha
  let g : codeGroup := codeT^n.val
  let v : QuaternaryWord := monomialHom g.val w
  have hv : v∈quaternaryCode := (g.prop w).mp hw
  have hv16 : euclideanWeight v=16 := (monomial_euclideanWeight g.val w).trans h16
  have hvf : admissibleFourSupport (reduce v) := by
    rcases quaternary_minimum_support_cases v hv hv16 with h|h
    · exact h
    · have hc := codeAction_activeBlocks_card g w
      change (activeBlocks (reduce v)).card=(activeBlocks (reduce w)).card at hc
      rw [heavy_activeBlocks_card _ h,four_minimum_activeBlocks_card w hw h16 ⟨a,ε,hr,hε,hs⟩] at hc
      omega
  obtain ⟨a',δ,hrv,hδ,hsδ⟩ := hvf
  have hp (r : Fin 7) : dot a'.val (rowLabel r).val=dot (binaryLabel 1) (rowLabel r).val := by
    have hh := fourNormal_pair δ a'.val (rowLabel r) 0
    simp only [zero_add] at hh
    rw [←hrv] at hh
    have ht := codeT_transported_pair n.val w ε a.val hr r
    exact hh.symm.trans (ht.trans (hn r))
  have ha' : a'.val=binaryLabel 1 := by
    funext i
    obtain ⟨r,hr⟩ := rowLabel_bijective.2 (basisPoint i)
    have hi := hp r
    rw [hr,dot_comm a'.val,dot_basisPoint,dot_comm (binaryLabel 1),dot_basisPoint] at hi
    exact hi
  rw [ha'] at hrv hδ
  obtain ⟨h,hh⟩ := fourLocal_fixed_label_word_orbit v hv hv16 δ hδ hsδ hrv
  let t : FourLocalStabilizer := ⟨g,codeT_pow_local_fix n.val⟩
  refine ⟨t⁻¹*h,?_⟩
  change monomialHom (g.val⁻¹*h.val.val) (quaternarySeed (3,0,0,0))=w
  rw [map_mul]
  change monomialHom g.val⁻¹ (monomialHom h.val.val (quaternarySeed (3,0,0,0)))=w
  rw [hh]
  change monomialHom g.val⁻¹ (monomialHom g.val w)=w
  simp

theorem fourLocal_minimum_words_transitive (v w : QuaternaryWord)
    (hv : v∈quaternaryCode) (hw : w∈quaternaryCode)
    (hv16 : euclideanWeight v=16) (hw16 : euclideanWeight w=16)
    (hvf : admissibleFourSupport (reduce v)) (hwf : admissibleFourSupport (reduce w))
    (hvzero : ∀x : E,reduce v (rowLabel 0,x)=0) (hwzero : ∀x : E,reduce w (rowLabel 0,x)=0) :
    ∃g : FourLocalStabilizer,monomialHom g.val.val v=w := by
  obtain ⟨g,hg⟩ := fourLocal_minimum_word_orbit v hv hv16 hvf hvzero
  obtain ⟨h,hh⟩ := fourLocal_minimum_word_orbit w hw hw16 hwf hwzero
  refine ⟨h*g⁻¹,?_⟩
  change monomialHom (h.val.val*g.val.val⁻¹) v=w
  rw [map_mul,←hg]
  simpa using hh

end Atlas.Rudvalis
