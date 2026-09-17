import Atlas.Conway.EisensteinUnitResidueSeparation
import Atlas.Conway.EisensteinTriadUnitParameters

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem eisensteinWordResidue_singleton (i : Fin 12) :
    eisensteinWordResidue (Pi.single i 1)=Pi.single i 1 := by
  ext j
  simp [eisensteinWordResidue,Pi.single_apply]

theorem eisensteinPairUnit_syndrome (b : Bool) (p : EisensteinOrderedPair) :
    ternarySyndromeClass (eisensteinWordResidue (eisensteinPairUnitA b p))=
      (ternaryPairSyndrome ⟨eisensteinPairSupport p,eisensteinPairSupport_mem p⟩).val := by
  congr 1
  ext j
  by_cases h : j ∈ eisensteinPairSupport p <;> simp [eisensteinPairUnitA_residue,ternaryPairWord,ternaryTriadWord,h]

theorem eisensteinHeavy_pair_disjoint (b : Bool) :
    Disjoint eisensteinHeavyUnitFrames (eisensteinPairUnitFrames b) := by
  apply Set.disjoint_left.mpr
  rintro F ⟨⟨i,t⟩,hF⟩ ⟨⟨p,s⟩,hG⟩
  have he := eisensteinOneModThree_frame_syndrome (eisensteinHeavyUnitVector i)
    (eisensteinPairUnitVector b p) (Pi.single i 1) (eisensteinPairUnitA b p)
    (fun _ => rfl) (fun _ => rfl) t s (hF.trans hG.symm)
  rw [eisensteinWordResidue_singleton,eisensteinPairUnit_syndrome] at he
  have hc : ternarySingletonSyndrome i=
      ternaryPairSyndrome ⟨eisensteinPairSupport p,eisensteinPairSupport_mem p⟩ := Subtype.ext he
  exact Finset.disjoint_left.mp ternarySmallSyndromes_disjoint
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    (Finset.mem_image.mpr ⟨⟨eisensteinPairSupport p,eisensteinPairSupport_mem p⟩,Finset.mem_univ _,hc.symm⟩)

theorem eisensteinHeavy_triad_disjoint (r : Fin 3) :
    Disjoint eisensteinHeavyUnitFrames (eisensteinTriadUnitFrames r) := by
  apply Set.disjoint_left.mpr
  rintro F ⟨⟨i,t⟩,hF⟩ ⟨⟨e,s⟩,hG⟩
  have he := eisensteinOneModThree_frame_syndrome (eisensteinHeavyUnitVector i)
    (eisensteinTriadUnitVector r e) (Pi.single i 1) (eisensteinTriadUnitA r e)
    (fun _ => rfl) (fun _ => rfl) t s (hF.trans hG.symm)
  rw [eisensteinWordResidue_singleton,eisensteinTriadUnitA_residue] at he
  have hc : ternarySingletonSyndrome i=ternaryOrientedSyndrome (eisensteinEmbeddingOriented e) := Subtype.ext he
  exact Finset.disjoint_left.mp ternarySingleton_oriented_disjoint
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    (Finset.mem_image.mpr ⟨eisensteinEmbeddingOriented e,Finset.mem_univ _,hc.symm⟩)

theorem eisensteinPair_triad_disjoint (b : Bool) (r : Fin 3) :
    Disjoint (eisensteinPairUnitFrames b) (eisensteinTriadUnitFrames r) := by
  apply Set.disjoint_left.mpr
  rintro F ⟨⟨p,t⟩,hF⟩ ⟨⟨e,s⟩,hG⟩
  have he := eisensteinOneModThree_frame_syndrome (eisensteinPairUnitVector b p)
    (eisensteinTriadUnitVector r e) (eisensteinPairUnitA b p) (eisensteinTriadUnitA r e)
    (fun _ => rfl) (fun _ => rfl) t s (hF.trans hG.symm)
  rw [eisensteinPairUnit_syndrome,eisensteinTriadUnitA_residue] at he
  have hc : ternaryPairSyndrome ⟨eisensteinPairSupport p,eisensteinPairSupport_mem p⟩=
      ternaryOrientedSyndrome (eisensteinEmbeddingOriented e) := Subtype.ext he
  exact Finset.disjoint_left.mp ternaryPair_oriented_disjoint
    (Finset.mem_image.mpr ⟨⟨eisensteinPairSupport p,eisensteinPairSupport_mem p⟩,Finset.mem_univ _,rfl⟩)
    (Finset.mem_image.mpr ⟨eisensteinEmbeddingOriented e,Finset.mem_univ _,hc.symm⟩)

end Atlas.Conway
