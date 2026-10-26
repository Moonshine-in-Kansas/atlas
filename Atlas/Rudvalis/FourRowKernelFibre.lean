import Atlas.Rudvalis.CodeRowCrossStabilizer
import Atlas.Rudvalis.CoupleFourFibre

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

 theorem codeRowKernel_mem_of_rows (g : codeGroup)
    (hg : ∀z : Coordinate,(g.val.right z).1=z.1) : g∈codeRowKernel := by
  change codeBlockLinearHom g=1
  apply LinearEquiv.ext
  intro x
  by_cases hx : x=0
  · subst x; simp
  · let p : Point := ⟨x,hx⟩
    have h := codeBlockLinear_coordinates g (p,0)
    rw [hg] at h
    exact h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem fourLocalOriginal_rows (z : SeedCoordinate) :
    (fourLocalOriginalA.right z).1=z.1 ∧ (fourLocalOriginalB.right z).1=z.1 := by
  decide +kernel +revert

theorem fourLocalCode_mem_rowKernel : fourLocalCodeA∈codeRowKernel ∧ fourLocalCodeB∈codeRowKernel := by
  have hgen (g : codeGroup) (h : SignedCoordinates SeedCoordinate)
      (hg : g.val=seedConjugateHom h) (hh : ∀z,(h.right z).1=z.1) : g∈codeRowKernel := by
    apply codeRowKernel_mem_of_rows
    intro z
    obtain ⟨z,rfl⟩ := originalCoordinateEquiv.surjective z
    rw [hg]
    change ((seedConjugateMonomial h).right (originalCoordinateEquiv z)).1=_
    rw [seedConjugateMonomial_right,original_congr_apply,originalCoordinateEquiv_row,hh]
    rfl
  exact ⟨hgen _ _ fourLocalCodeA_transport (fun z=>(fourLocalOriginal_rows z).1),
    hgen _ _ fourLocalCodeB_transport (fun z=>(fourLocalOriginal_rows z).2)⟩

theorem fourLocalOrbitElement_mem_rowKernel (a : E) (b c : Bool) :
    fourLocalOrbitElement a b c∈codeRowKernel := by
  apply codeRowKernel.mul_mem
  · apply codeRowKernel_mem_of_rows
    intro z; rfl
  · change (if b then fourLocalCodeA else 1)*(if c then fourLocalCodeB else 1)∈codeRowKernel
    apply codeRowKernel.mul_mem
    · split_ifs; exact fourLocalCode_mem_rowKernel.1; exact codeRowKernel.one_mem
    · split_ifs; exact fourLocalCode_mem_rowKernel.2; exact codeRowKernel.one_mem

 theorem four_rowKernel_same_residue_transitive (v w : QuaternaryWord)
    (hv : v∈quaternaryCode) (hw : w∈quaternaryCode)
    (hv16 : euclideanWeight v=16) (hw16 : euclideanWeight w=16)
    (hf : admissibleFourSupport (reduce v)) (he : reduce v=reduce w) :
    ∃t : codeRowKernel,monomialHom t.val.val v=w := by
  have hs : admissibleFourSupport (reduce (quaternarySeed (3,0,0,0))) := by
    have hb : reduce (quaternarySeed (3,0,0,0))=
        binaryNormalMap (fourLocalBaseConstants false,outerMatrix (binaryLabel 1) (binaryLabel 1),0) :=
      by simpa using fourLocal_base_support false
    exact ⟨⟨binaryLabel 1,by decide⟩,fourLocalBaseConstants false,hb,
      by intro p hp; exact (fourLocalBaseConstants_data false).1 p hp,
      by exact (fourLocalBaseConstants_data false).2.1⟩
  obtain ⟨g,hg⟩ := four_minimum_transitive (quaternarySeed (3,0,0,0)) v
    (quaternaryCode_seed _) hv fourthSeed_weight hv16 hs hf
  let u := monomialHom g.val⁻¹ w
  have hu : u∈quaternaryCode := (g⁻¹).prop w |>.mp hw
  have hu16 : euclideanWeight u=16 := (monomial_euclideanWeight _ _).trans hw16
  have hur : reduce u=fourPlaneSeedResidue := by
    have h := monomial_reduce_congr g⁻¹ w v he.symm
    change reduce u=reduce (monomialHom g.val⁻¹ v) at h
    rw [←hg] at h
    simpa using h.trans (by simpa using fourthSeed_residue)
  obtain ⟨⟨a,b,c⟩,habc⟩ := fourLocalOrbitLift_surjective ⟨⟨u,hu⟩,hu16,hur⟩
  let h := fourLocalOrbitElement a b c
  have hh : monomialHom h.val (quaternarySeed (3,0,0,0))=u :=
    congrArg (fun z : minimumLift fourPlaneSeedResidue=>z.val.val) habc
  have hmem : g*h*g⁻¹∈codeRowKernel := by
    change codeBlockLinearHom (g*h*g⁻¹)=1
    have he : codeBlockLinearHom h=1 := fourLocalOrbitElement_mem_rowKernel a b c
    rw [map_mul,map_mul,map_inv,he,mul_one,mul_inv_cancel]
  refine ⟨⟨g*h*g⁻¹,hmem⟩,?_⟩
  change monomialHom (g.val*h.val*g.val⁻¹) v=w
  rw [map_mul,map_mul]
  change monomialHom g.val (monomialHom h.val (monomialHom g.val⁻¹ v))=w
  rw [←hg]
  have hinv : monomialHom g.val⁻¹ (monomialHom g.val (quaternarySeed (3,0,0,0)))=
      quaternarySeed (3,0,0,0) := by simp
  rw [hinv,hh]
  change monomialHom g.val (monomialHom g.val⁻¹ w)=w
  simp

end Atlas.Rudvalis
