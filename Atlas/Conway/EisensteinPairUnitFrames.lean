import Atlas.Conway.EisensteinUnitResidueFrames
import Atlas.Codes.TernarySyndromeSupports

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev EisensteinOrderedPair := {p : Fin 12 × Fin 12 // p.1≠p.2}

def eisensteinPairChirality (b : Bool) : Eisenstein := if b then 1+eisensteinOmega else -eisensteinOmega

def eisensteinPairUnitA (b : Bool) (p : EisensteinOrderedPair) : EisensteinCoordinates :=
  eisensteinPairChirality b • Pi.single p.val.1 1-Pi.single p.val.2 1

def eisensteinPairUnitCoordinates (b : Bool) (p : EisensteinOrderedPair) : EisensteinCoordinates :=
  fun j => 1+3*eisensteinPairUnitA b p j

theorem eisensteinPairUnitA_sum (b : Bool) (p : EisensteinOrderedPair) :
    ∑ j, eisensteinPairUnitA b p j = eisensteinPairChirality b-1 := by
  simp [eisensteinPairUnitA,Pi.smul_apply,smul_eq_mul,Finset.sum_sub_distrib,← Finset.mul_sum]

theorem eisensteinPairUnit_mem (b : Bool) (p : EisensteinOrderedPair) :
    eisensteinPairUnitCoordinates b p ∈ eisensteinLeechModule := by
  apply eisensteinOneModThree_mem
  rw [eisensteinPairUnitA_sum]
  refine ⟨(if b then -1 else -2)-3*eisensteinOmega,?_⟩
  have h : ∀ b : Bool, 5+(eisensteinPairChirality b-1) =
      eisensteinTheta*((if b then -1 else -2)-3*eisensteinOmega) := by decide +kernel
  exact h b

def eisensteinPairUnitLattice (b : Bool) (p : EisensteinOrderedPair) : EisensteinLattice :=
  ⟨eisensteinPairUnitCoordinates b p,eisensteinPairUnit_mem b p⟩

theorem eisensteinPairUnit_oneModThree (b : Bool) (p : EisensteinOrderedPair) :
    EisensteinOneModThree (eisensteinPairUnitLattice b p) := ⟨eisensteinPairUnitA b p,fun _ => rfl⟩

theorem eisensteinPairUnit_norm (b : Bool) (p : EisensteinOrderedPair) :
    eisensteinNorm (eisensteinPairUnitLattice b p)=6 := by
  have hc (j : Fin 12) : (eisensteinPairUnitCoordinates b p j).norm =
      1+12*(Pi.single p.val.1 (1 : ℤ) : Fin 12 → ℤ) j+
        3*(Pi.single p.val.2 (1 : ℤ) : Fin 12 → ℤ) j := by
    have h13 : (1+3*eisensteinPairChirality b).norm=13 := by cases b <;> decide +kernel
    by_cases hj : j=p.val.1
    · have hk : j≠p.val.2 := by rw [hj]; exact p.property
      simp [eisensteinPairUnitCoordinates,eisensteinPairUnitA,Pi.smul_apply,Pi.single_apply,hj,hk,h13,p.property,Ne.symm p.property]
    · by_cases hk : j=p.val.2
      · simp [eisensteinPairUnitCoordinates,eisensteinPairUnitA,Pi.smul_apply,Pi.single_apply,hj,hk,p.property,Ne.symm p.property,
          show (1+ -3 : Eisenstein).norm=4 by decide +kernel]
      · simp [eisensteinPairUnitCoordinates,eisensteinPairUnitA,Pi.smul_apply,Pi.single_apply,hj,hk]
  unfold eisensteinNorm
  rw [eisensteinBilinear_self_sum_norm]
  change (2/9 : ℚ)*(∑ j, (eisensteinToRational (eisensteinPairUnitCoordinates b p j)).norm)=6
  simp_rw [eisensteinToRational_norm,hc]
  push_cast
  norm_num [Finset.sum_add_distrib,← Finset.mul_sum,Pi.single_apply]

def eisensteinPairUnitVector (b : Bool) (p : EisensteinOrderedPair) : EisensteinShell 6 :=
  ⟨eisensteinPairUnitLattice b p,eisensteinPairUnit_norm b p⟩

def eisensteinPairUnitFrame (b : Bool) (p : EisensteinOrderedPair) (t : ternaryGolay) : EisensteinFrame :=
  eisensteinFrameOfVector (eisensteinCodePhaseShell t (eisensteinPairUnitVector b p))

def eisensteinPairSupport (p : EisensteinOrderedPair) : Finset (Fin 12) := {p.val.1,p.val.2}

theorem eisensteinPairUnitA_residue (b : Bool) (p : EisensteinOrderedPair) (j : Fin 12) :
    eisensteinWordResidue (eisensteinPairUnitA b p) j =
      if j ∈ eisensteinPairSupport p then -1 else 0 := by
  have hb : eisensteinResidue (eisensteinPairChirality b)= -1 := by cases b <;> decide +kernel
  by_cases hj : j=p.val.1
  · have hk : j≠p.val.2 := by rw [hj]; exact p.property
    simp [eisensteinPairUnitA,eisensteinWordResidue,Pi.smul_apply,Pi.single_apply,hj,hk,p.property,Ne.symm p.property,
      eisensteinPairSupport,hb,p.property,Ne.symm p.property]
  · by_cases hk : j=p.val.2
    · simp [eisensteinPairUnitA,eisensteinWordResidue,Pi.smul_apply,Pi.single_apply,hj,hk,p.property,Ne.symm p.property,
        eisensteinPairSupport,hb,p.property,Ne.symm p.property]
    · simp [eisensteinPairUnitA,eisensteinWordResidue,Pi.smul_apply,Pi.single_apply,hj,hk,p.property,Ne.symm p.property,
        eisensteinPairSupport,hb,p.property,Ne.symm p.property]


theorem eisensteinPairUnitA_support (b : Bool) (p : EisensteinOrderedPair) :
    ternarySupport (eisensteinWordResidue (eisensteinPairUnitA b p)) = eisensteinPairSupport p := by
  ext j
  simp only [ternarySupport,Finset.mem_filter,Finset.mem_univ,true_and,eisensteinPairUnitA_residue]
  by_cases h : j ∈ eisensteinPairSupport p <;> simp [h]

theorem eisensteinPairChirality_mod_three (b c : Bool)
    (h : (3 : Eisenstein) ∣ eisensteinPairChirality b-eisensteinPairChirality c) : b=c := by
  cases b <;> cases c <;> try rfl
  all_goals
    obtain ⟨d,hd⟩ := h
    have hr := congrArg QuadraticAlgebra.re hd
    norm_num [eisensteinPairChirality,eisensteinOmega,QuadraticAlgebra.omega] at hr
    norm_num only [show (1 : Eisenstein).re=1 by rfl,
      show (3 : Eisenstein).re=3 by rfl,show (3 : Eisenstein).im=0 by rfl,
      zero_mul,neg_zero,add_zero] at hr
    omega

theorem eisensteinPairUnit_class_iff (b c : Bool) (p q : EisensteinOrderedPair) :
    eisensteinClass (eisensteinPairUnitLattice b p)=eisensteinClass (eisensteinPairUnitLattice c q) ↔
      b=c ∧ eisensteinPairSupport p=eisensteinPairSupport q := by
  rw [eisensteinOneModThree_class_iff _ _ (eisensteinPairUnitA b p) (eisensteinPairUnitA c q)
    (fun _ => rfl) (fun _ => rfl)]
  have hr : eisensteinWordResidue (eisensteinPairUnitA b p-eisensteinPairUnitA c q) =
      eisensteinWordResidue (eisensteinPairUnitA b p)-eisensteinWordResidue (eisensteinPairUnitA c q) := by
    funext j; exact map_sub eisensteinResidue _ _
  have hs : (∑ j, (eisensteinPairUnitA b p-eisensteinPairUnitA c q) j) =
      eisensteinPairChirality b-eisensteinPairChirality c := by
    simp only [Pi.sub_apply,Finset.sum_sub_distrib,eisensteinPairUnitA_sum]
    ring
  rw [hr,hs]
  constructor
  · rintro ⟨hc,hd⟩
    refine ⟨eisensteinPairChirality_mod_three b c hd,?_⟩
    have he := ternarySyndrome_small_support _ _ (by
      rw [eisensteinPairUnitA_support,eisensteinPairUnitA_support]
      simp [eisensteinPairSupport,Finset.card_pair p.property,Finset.card_pair q.property])
      ((ternarySyndromeClass_eq_iff _ _).mpr hc)
    simpa only [eisensteinPairUnitA_support] using congrArg ternarySupport he
  · rintro ⟨rfl,hp⟩
    refine ⟨?_,by simp⟩
    have he : eisensteinWordResidue (eisensteinPairUnitA b p) =
        eisensteinWordResidue (eisensteinPairUnitA b q) := by
      funext j
      rw [eisensteinPairUnitA_residue,eisensteinPairUnitA_residue,hp]
    rw [he,sub_self]
    exact ternaryGolay.zero_mem

theorem eisensteinPairUnitFrame_eq_iff (b c : Bool) (p q : EisensteinOrderedPair) (t s : ternaryGolay) :
    eisensteinPairUnitFrame b p t=eisensteinPairUnitFrame c q s ↔
      b=c ∧ eisensteinPairSupport p=eisensteinPairSupport q ∧ t-s ∈ ternaryConstants := by
  rw [eisensteinPairUnitFrame,eisensteinPairUnitFrame,
    eisensteinOneModThree_frame_phase_iff _ _ (eisensteinPairUnit_oneModThree b p)
      (eisensteinPairUnit_oneModThree c q)]
  have he : eisensteinFrameOfVector (eisensteinPairUnitVector b p) =
      eisensteinFrameOfVector (eisensteinPairUnitVector c q) ↔
      eisensteinClass (eisensteinPairUnitLattice b p)=eisensteinClass (eisensteinPairUnitLattice c q) := by
    constructor
    · intro h
      exact ((eisensteinFramePair_eq_iff _ _).mp (congrArg Subtype.val h)).resolve_right
        (eisensteinClass_not_neg_of_residue_one _ _
          (eisensteinOneModThree_residue _ (eisensteinPairUnit_oneModThree b p) 0)
          (eisensteinOneModThree_residue _ (eisensteinPairUnit_oneModThree c q) 0))
    · intro h
      exact Subtype.ext (congrArg eisensteinFramePair h)
  rw [he,eisensteinPairUnit_class_iff,and_assoc]

end Atlas.Conway
