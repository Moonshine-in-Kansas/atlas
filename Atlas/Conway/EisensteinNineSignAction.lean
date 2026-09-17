import Atlas.Conway.EisensteinNineSignFrames
import Atlas.Conway.EisensteinHeavyUnitOrbit
import Atlas.Conway.EisensteinHexadPhaseAction

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

 theorem eisensteinConstantHexad_code_sum (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (a : ternaryGolay) : (∑ i ∈ s,a.val i)=0 := by
  have h := ternaryGolay_selfOrthogonal a.property (ternaryTriadWord s)
    ((mem_ternaryConstantHexads s).mp hs).2
  simpa [ternaryDot,dotProductBilin,dotProduct,ternaryTriadWord,Finset.sum_filter] using h

 theorem eisensteinConstantNineForm_phase (s : Finset (Fin 12)) (k : Fin 12)
    (b z : ZMod 3) (t a : TernaryWord) :
    eisensteinDiagonal a (eisensteinTheta • eisensteinConstantNineForm s k b z t)=
      eisensteinTheta • eisensteinConstantNineForm s k b (z+a k) (t+a) := by
  funext i
  by_cases hik : i=k
  · subst i
    by_cases hi : k ∈ s <;>
      simp [eisensteinDiagonal,eisensteinConstantNineForm,Pi.smul_apply,smul_eq_mul,hi,
        eisensteinPhase_add,Pi.add_apply] <;> ring
  · by_cases hi : i ∈ s <;>
      simp [eisensteinDiagonal,eisensteinConstantNineForm,Pi.smul_apply,smul_eq_mul,hi,hik,
        eisensteinPhase_add,Pi.add_apply] <;> ring

 theorem eisensteinNineSignFrame_phase (b : ZMod 3) (F : EisensteinFrame)
    (hF : EisensteinNineSignFrame b F) (a : ternaryGolay) :
    EisensteinNineSignFrame b (eisensteinPhaseIsometries (Multiplicative.ofAdd a) • F) := by
  obtain ⟨s,hs,k,hk,z,t,ht,x,hx,hF⟩ := hF
  refine ⟨s,hs,k,hk,z+a.val k,t+a.val,?_,
    eisensteinShellAction (eisensteinPhaseIsometries (Multiplicative.ofAdd a)) 6 x,?_,?_⟩
  · simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib,ht,eisensteinConstantHexad_code_sum s hs a,add_zero]
  · change (eisensteinIntegralAction _ x.val).val=_
    rw [eisensteinIntegralAction_phase,hx,eisensteinConstantNineForm_phase]
  · rw [← eisensteinFrameAction_vector,hF]

 theorem eisensteinNineSignFrame_coordinate (b : ZMod 3) (F : EisensteinFrame)
    (hF : EisensteinNineSignFrame b F) (g : TernaryPureAutomorphism) :
    EisensteinNineSignFrame b (eisensteinCoordinateIsometries g • F) := by
  obtain ⟨s,hs,k,hk,z,t,ht,x,hx,hF⟩ := hF
  let r := s.map g.val.toEmbedding
  let v : TernaryWord := fun i => t (g.val.symm i)
  have hkr : g.val k ∉ r := by simpa [r,Finset.mem_map_equiv] using hk
  refine ⟨r,ternaryConstantHexads_permute g s hs,g.val k,hkr,z,v,?_,
    eisensteinShellAction (eisensteinCoordinateIsometries g) 6 x,?_,?_⟩
  · simpa [r,v,Finset.sum_map] using ht
  · funext i
    change (eisensteinIntegralAction _ x.val).val i=_
    rw [eisensteinIntegralAction_coordinate_apply,hx]
    have he : g.val.symm i=k ↔ i=g.val k := by
      constructor
      · intro h; rw [← h,Equiv.apply_symm_apply]
      · intro h; rw [h,Equiv.symm_apply_apply]
    simp only [Pi.smul_apply,smul_eq_mul,eisensteinConstantNineForm]
    simp [r,v,Finset.mem_map_equiv,he]
  · rw [← eisensteinFrameAction_vector,hF]

/-- The actual full monomial frame stabilizer preserves the intrinsic correction sign. -/
theorem eisensteinNineSignFrame_preserved (b : ZMod 3)
    (g : eisensteinCoordinateFrameStabilizer) (F : EisensteinFrame)
    (hF : EisensteinNineSignFrame b F) : EisensteinNineSignFrame b (g.val • F) := by
  obtain ⟨p,rfl⟩ := eisensteinFrameFromParameters_surjective g
  change EisensteinNineSignFrame b (eisensteinMonomialParameterIsometry p • F)
  rw [eisensteinMonomialParameterIsometry,mul_smul,mul_smul]
  have h := eisensteinNineSignFrame_phase b _ (eisensteinNineSignFrame_coordinate b F hF p.2.2) p.2.1
  cases hp : p.1 <;> simpa [hp,eisensteinSignIsometry_frame] using h

end Atlas.Conway
