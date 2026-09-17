import Atlas.Conway.EisensteinBalancedCoordinateAction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

 theorem eisensteinBalancedBaseFrame_positive (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) :
    ∃ d : TernaryBalancedWords, ∃ k : ternarySupport d.val.val,
      d.val.val k.val=1 ∧ eisensteinBalancedBaseFrame d k=eisensteinBalancedBaseFrame c j := by
  have hn : c.val.val j.val≠0 := (Finset.mem_filter.mp j.prop).2
  have hc : c.val.val j.val=1 ∨ c.val.val j.val=2 := by
    exact (show ∀ a : ZMod 3,a≠0 → a=1 ∨ a=2 by decide +kernel) _ hn
  rcases hc with hc|hc
  · exact ⟨c,j,hc,rfl⟩
  · refine ⟨ternaryBalancedNeg c,eisensteinBalancedNegPosition c j,?_,
      eisensteinBalancedBaseFrame_neg c j⟩
    change -c.val.val j.val=1
    rw [hc]
    decide

theorem eisensteinBalancedBaseFrame_transitive (c d : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (k : ternarySupport d.val.val) :
    ∃ g : eisensteinCoordinateFrameStabilizer,
      g.val • eisensteinBalancedBaseFrame c j=eisensteinBalancedBaseFrame d k := by
  obtain ⟨c',j',hc,hcF⟩ := eisensteinBalancedBaseFrame_positive c j
  obtain ⟨d',k',hd,hdF⟩ := eisensteinBalancedBaseFrame_positive d k
  obtain ⟨g,hg,hjk⟩ := ternaryBalanced_positive_flags_transitive c' d' j'.val k'.val hc hd
  refine ⟨eisensteinFrameFromParameters (false,0,g),?_⟩
  change eisensteinMonomialParameterIsometry (false,0,g) • _ = _
  have he : eisensteinMonomialParameterIsometry (false,0,g)=eisensteinCoordinateIsometries g := by
    simp [eisensteinMonomialParameterIsometry]
  rw [he,← hcF,← hdF]
  exact eisensteinBalancedBaseFrame_coordinate c' d' j' k' g hg hjk

def eisensteinBalancedLocalPhase (t : ternaryGolay) : eisensteinCoordinateFrameStabilizer :=
  eisensteinFrameFromParameters (false,t,1)

theorem eisensteinBalancedLocalPhase_val (t : ternaryGolay) :
    (eisensteinBalancedLocalPhase t).val=eisensteinPhaseIsometries (Multiplicative.ofAdd t) := by
  change eisensteinMonomialParameterIsometry (false,t,1)=_
  simp [eisensteinMonomialParameterIsometry]

/-- The full coordinate-frame stabilizer is transitive on the 17820 balanced-heavy frames. -/
theorem eisensteinBalancedFamily_transitive (F G : EisensteinFrame)
    (hF : F ∈ eisensteinBalancedFamily) (hG : G ∈ eisensteinBalancedFamily) :
    ∃ g : eisensteinCoordinateFrameStabilizer,g.val • F=G := by
  obtain ⟨p,rfl⟩ := eisensteinBalancedFamily_mem_iff F |>.mp hF
  obtain ⟨q,rfl⟩ := eisensteinBalancedFamily_mem_iff G |>.mp hG
  obtain ⟨t,ht⟩ := eisensteinBalancedFrame_phase_exists p
  obtain ⟨s,hs⟩ := eisensteinBalancedFrame_phase_exists q
  obtain ⟨g,hg⟩ := eisensteinBalancedBaseFrame_transitive p.1 q.1 p.2.1 q.2.1
  refine ⟨eisensteinBalancedLocalPhase s*g*(eisensteinBalancedLocalPhase t)⁻¹,?_⟩
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,mul_smul,eisensteinBalancedLocalPhase_val]
  rw [← ht,inv_smul_smul,hg,hs]

end Atlas.Conway
