import Atlas.Fischer.CountingOctadParameters
import Atlas.Fischer.CountingHexacodeRows

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def countingPairMask (h : hexacode) (r : P6) (i : Fin 6) : Bit :=
  r.val i+qK (h.val (hexPos i))

theorem countingPairMask_even (h : hexacode) (r : P6) : ∑ i, countingPairMask h r i=0 := by
  unfold countingPairMask
  rw [Finset.sum_add_distrib,(parityCode_mem 5 _).mp r.property,zero_add]
  change (∑ i : Fin 6, qK (h.val (hexIndexEquiv.symm i)))=0
  rw [Equiv.sum_comp hexIndexEquiv.symm (fun j : HexIndex => qK (h.val j))]
  exact hexacode_isotropic h.val h.property

theorem countingTypeA_mask_weight (p : CountingTypeA) : hammingNorm p.val.val=2 := by
  have h := p.property
  have he : c0Encoder (0,p.val)=rho p.val.val := by simp [c0Encoder]
  rw [he,rho_weight] at h
  omega

theorem countingTypeB_zero_off_support (p : CountingTypeB) (i : Fin 6)
    (hi : p.1.val.val (hexPos i)=0) : p.2.val.val i=0 := by
  have h := c0Encoder_weight_formula p.1.val p.2.val
  rw [p.2.property,p.1.property] at h
  have hc : (Finset.univ.filter (fun j : Fin 6 =>
      p.1.val.val (hexIndexEquiv.symm j)=0 ∧ p.2.val.val j ≠ 0)).card=0 := by omega
  by_contra hn
  have hm : i ∈ Finset.univ.filter (fun j : Fin 6 =>
      p.1.val.val (hexIndexEquiv.symm j)=0 ∧ p.2.val.val j ≠ 0) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hn⟩
  rw [Finset.card_eq_zero.mp hc] at hm
  exact Finset.notMem_empty _ hm

theorem countingTypeB_pairMask_zero_off_support (p : CountingTypeB) (i : Fin 6)
    (hi : p.1.val.val (hexPos i)=0) : countingPairMask p.1.val p.2.val i=0 := by
  rw [countingPairMask,countingTypeB_zero_off_support p i hi,hi]
  decide

def countingOddMask (p : CountingTypeC) : Fin 6 → Bit := p.2.val.val+oddMask p.1.val

theorem countingOddMask_weight (p : CountingTypeC) : hammingNorm (countingOddMask p)=1 := by
  have h := odd_word_weight p.1 p.2.val
  rw [p.2.property] at h
  change 8=6+2*hammingNorm (countingOddMask p) at h
  omega

theorem countingOddMask_singleton (p : CountingTypeC) :
    ∃ i : Fin 6, countingOddMask p=Pi.single i 1 := by
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp (countingOddMask_weight p)
  refine ⟨i,?_⟩
  apply binarySupportEquiv.injective
  change support (countingOddMask p)=support (Pi.single i (1 : Bit))
  change support (countingOddMask p)={i} at hi
  rw [hi]
  ext j
  simp [support,Pi.single_apply]

def countingDistinguishedColumn (p : CountingTypeC) : Fin 6 :=
  Classical.choose (countingOddMask_singleton p)

theorem countingDistinguishedColumn_mask (p : CountingTypeC) :
    countingOddMask p=Pi.single (countingDistinguishedColumn p) 1 :=
  Classical.choose_spec (countingOddMask_singleton p)

end Atlas.Fischer
