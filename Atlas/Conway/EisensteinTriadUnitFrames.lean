import Atlas.Conway.EisensteinPairUnitRecognition
import Atlas.Codes.TernaryOrientedAction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def eisensteinTriadChirality (r : Fin 3) (k : Fin 2) : Eisenstein :=
  if k.val<r.val then eisensteinOmega else -1-eisensteinOmega

def eisensteinTriadUnitA (r : Fin 3) (e : Fin 3 ↪ Fin 12) : EisensteinCoordinates :=
  eisensteinTriadChirality r 0 • Pi.single (e 0) 1+
    eisensteinTriadChirality r 1 • Pi.single (e 1) 1-Pi.single (e 2) 1

def eisensteinTriadUnitCoordinates (r : Fin 3) (e : Fin 3 ↪ Fin 12) : EisensteinCoordinates :=
  fun j => 1+3*eisensteinTriadUnitA r e j

def eisensteinTriadChiralitySum (r : Fin 3) : Eisenstein :=
  eisensteinTriadChirality r 0+eisensteinTriadChirality r 1-1

theorem eisensteinTriadChirality_residue (r : Fin 3) (k : Fin 2) :
    eisensteinResidue (eisensteinTriadChirality r k)=1 := by revert r k; decide +kernel

theorem eisensteinTriadChirality_norm (r : Fin 3) (k : Fin 2) :
    (1+3*eisensteinTriadChirality r k).norm=7 := by revert r k; decide +kernel

theorem eisensteinTriadUnitA_sum (r : Fin 3) (e : Fin 3 ↪ Fin 12) :
    ∑ j, eisensteinTriadUnitA r e j=eisensteinTriadChiralitySum r := by
  simp [eisensteinTriadUnitA,eisensteinTriadChiralitySum,Pi.smul_apply,smul_eq_mul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]

theorem eisensteinTriadUnit_mem (r : Fin 3) (e : Fin 3 ↪ Fin 12) :
    eisensteinTriadUnitCoordinates r e ∈ eisensteinLeechModule := by
  apply eisensteinOneModThree_mem
  rw [eisensteinTriadUnitA_sum]
  apply (eisensteinResidue_eq_zero _).mp
  have h : ∀ r : Fin 3, eisensteinResidue (5+eisensteinTriadChiralitySum r)=0 := by decide +kernel
  exact h r

def eisensteinTriadUnitLattice (r : Fin 3) (e : Fin 3 ↪ Fin 12) : EisensteinLattice :=
  ⟨eisensteinTriadUnitCoordinates r e,eisensteinTriadUnit_mem r e⟩

theorem eisensteinTriadUnit_oneModThree (r : Fin 3) (e : Fin 3 ↪ Fin 12) :
    EisensteinOneModThree (eisensteinTriadUnitLattice r e) := ⟨eisensteinTriadUnitA r e,fun _ => rfl⟩

theorem eisensteinTriadUnit_norm (r : Fin 3) (e : Fin 3 ↪ Fin 12) :
    eisensteinNorm (eisensteinTriadUnitLattice r e)=6 := by
  have h01 : e 0≠e 1 := e.injective.ne (by decide)
  have h02 : e 0≠e 2 := e.injective.ne (by decide)
  have h12 : e 1≠e 2 := e.injective.ne (by decide)
  have hc (j : Fin 12) : (eisensteinTriadUnitCoordinates r e j).norm =
      1+6*(Pi.single (e 0) (1 : ℤ) : Fin 12 → ℤ) j+
        6*(Pi.single (e 1) (1 : ℤ) : Fin 12 → ℤ) j+
          3*(Pi.single (e 2) (1 : ℤ) : Fin 12 → ℤ) j := by
    by_cases h0 : j=e 0
    · simp [eisensteinTriadUnitCoordinates,eisensteinTriadUnitA,Pi.smul_apply,Pi.single_apply,h0,
        h01,h02,eisensteinTriadChirality_norm]
    · by_cases h1 : j=e 1
      · simp [eisensteinTriadUnitCoordinates,eisensteinTriadUnitA,Pi.smul_apply,Pi.single_apply,h0,h1,
          Ne.symm h01,h12,eisensteinTriadChirality_norm]
      · by_cases h2 : j=e 2
        · simp [eisensteinTriadUnitCoordinates,eisensteinTriadUnitA,Pi.smul_apply,Pi.single_apply,h0,h1,h2,
            Ne.symm h02,Ne.symm h12,show (1+ -3 : Eisenstein).norm=4 by decide +kernel]
        · simp [eisensteinTriadUnitCoordinates,eisensteinTriadUnitA,Pi.smul_apply,Pi.single_apply,h0,h1,h2]
  unfold eisensteinNorm
  rw [eisensteinBilinear_self_sum_norm]
  change (2/9 : ℚ)*(∑ j, (eisensteinToRational (eisensteinTriadUnitCoordinates r e j)).norm)=6
  simp_rw [eisensteinToRational_norm,hc]
  push_cast
  norm_num [Finset.sum_add_distrib,← Finset.mul_sum,Pi.single_apply]

def eisensteinTriadUnitVector (r : Fin 3) (e : Fin 3 ↪ Fin 12) : EisensteinShell 6 :=
  ⟨eisensteinTriadUnitLattice r e,eisensteinTriadUnit_norm r e⟩

def eisensteinTriadUnitFrame (r : Fin 3) (e : Fin 3 ↪ Fin 12) (t : ternaryGolay) : EisensteinFrame :=
  eisensteinFrameOfVector (eisensteinCodePhaseShell t (eisensteinTriadUnitVector r e))

def eisensteinEmbeddingOriented (e : Fin 3 ↪ Fin 12) : TernaryOrientedTriad :=
  ⟨(Finset.univ.map e,e 2),(mem_ternaryOrientedTriads _).mpr
    ⟨by simp,Finset.mem_map.mpr ⟨(2 : Fin 3),Finset.mem_univ _,rfl⟩⟩⟩

theorem eisensteinTriadUnitA_residue (r : Fin 3) (e : Fin 3 ↪ Fin 12) :
    eisensteinWordResidue (eisensteinTriadUnitA r e) = ternaryOrientedWord (eisensteinEmbeddingOriented e).val := by
  funext j
  have h01 : e 0≠e 1 := e.injective.ne (by decide)
  have h02 : e 0≠e 2 := e.injective.ne (by decide)
  have h12 : e 1≠e 2 := e.injective.ne (by decide)
  have hm : j ∈ Finset.univ.map e ↔ j=e 0 ∨ j=e 1 ∨ j=e 2 := by
    simp [Finset.mem_map,Fin.exists_fin_succ,eq_comm]
  by_cases h0 : j=e 0
  · simp [eisensteinWordResidue,eisensteinTriadUnitA,eisensteinTriadChirality_residue,Pi.smul_apply,Pi.single_apply,
      ternaryOrientedWord,ternaryTriadWord,eisensteinEmbeddingOriented,hm,h0,h01,h02]
  · by_cases h1 : j=e 1
    · simp [eisensteinWordResidue,eisensteinTriadUnitA,eisensteinTriadChirality_residue,Pi.smul_apply,Pi.single_apply,
        ternaryOrientedWord,ternaryTriadWord,eisensteinEmbeddingOriented,hm,h0,h1,Ne.symm h01,h12]
    · by_cases h2 : j=e 2
      · simp [eisensteinWordResidue,eisensteinTriadUnitA,eisensteinTriadChirality_residue,Pi.smul_apply,Pi.single_apply,
          ternaryOrientedWord,ternaryTriadWord,eisensteinEmbeddingOriented,hm,h0,h1,h2,Ne.symm h02,Ne.symm h12]
        decide
      · simp [eisensteinWordResidue,eisensteinTriadUnitA,eisensteinTriadChirality_residue,Pi.smul_apply,Pi.single_apply,
          ternaryOrientedWord,ternaryTriadWord,eisensteinEmbeddingOriented,hm,h0,h1,h2]

theorem eisensteinTriadChirality_mod_three (r s : Fin 3)
    (h : (3 : Eisenstein) ∣ eisensteinTriadChiralitySum r-eisensteinTriadChiralitySum s) : r=s := by
  have hr : ∀ r : Fin 3, (eisensteinTriadChiralitySum r).re=(r.val : ℤ)-3 := by decide +kernel
  obtain ⟨d,hd⟩ := h
  have hd' := congrArg QuadraticAlgebra.re hd
  simp only [QuadraticAlgebra.re_sub,hr,QuadraticAlgebra.re_mul,
    show (3 : Eisenstein).re=3 by rfl,show (3 : Eisenstein).im=0 by rfl,
    zero_mul,add_zero] at hd'
  apply Fin.ext
  omega

theorem eisensteinTriadUnit_class_iff (r s : Fin 3) (e f : Fin 3 ↪ Fin 12) :
    eisensteinClass (eisensteinTriadUnitLattice r e)=eisensteinClass (eisensteinTriadUnitLattice s f) ↔
      r=s ∧ ternarySyndromeClass (ternaryOrientedWord (eisensteinEmbeddingOriented e).val)=
        ternarySyndromeClass (ternaryOrientedWord (eisensteinEmbeddingOriented f).val) := by
  rw [eisensteinOneModThree_class_iff _ _ (eisensteinTriadUnitA r e) (eisensteinTriadUnitA s f)
    (fun _ => rfl) (fun _ => rfl)]
  have hr : eisensteinWordResidue (eisensteinTriadUnitA r e-eisensteinTriadUnitA s f) =
      eisensteinWordResidue (eisensteinTriadUnitA r e)-eisensteinWordResidue (eisensteinTriadUnitA s f) := by
    funext j; exact map_sub eisensteinResidue _ _
  have hs : (∑ j, (eisensteinTriadUnitA r e-eisensteinTriadUnitA s f) j) =
      eisensteinTriadChiralitySum r-eisensteinTriadChiralitySum s := by
    simp only [Pi.sub_apply,Finset.sum_sub_distrib,eisensteinTriadUnitA_sum]
  rw [hr,hs,eisensteinTriadUnitA_residue,eisensteinTriadUnitA_residue,
    ← ternarySyndromeClass_eq_iff]
  constructor
  · rintro ⟨hc,hd⟩
    exact ⟨eisensteinTriadChirality_mod_three r s hd,hc⟩
  · rintro ⟨rfl,hc⟩
    exact ⟨hc,by simp⟩

theorem eisensteinTriadUnitFrame_eq_iff (r s : Fin 3) (e f : Fin 3 ↪ Fin 12) (t u : ternaryGolay) :
    eisensteinTriadUnitFrame r e t=eisensteinTriadUnitFrame s f u ↔
      r=s ∧ ternarySyndromeClass (ternaryOrientedWord (eisensteinEmbeddingOriented e).val)=
        ternarySyndromeClass (ternaryOrientedWord (eisensteinEmbeddingOriented f).val) ∧
          t-u ∈ ternaryConstants := by
  rw [eisensteinTriadUnitFrame,eisensteinTriadUnitFrame,
    eisensteinOneModThree_frame_phase_iff _ _ (eisensteinTriadUnit_oneModThree r e)
      (eisensteinTriadUnit_oneModThree s f)]
  have he : eisensteinFrameOfVector (eisensteinTriadUnitVector r e) =
      eisensteinFrameOfVector (eisensteinTriadUnitVector s f) ↔
      eisensteinClass (eisensteinTriadUnitLattice r e)=eisensteinClass (eisensteinTriadUnitLattice s f) := by
    constructor
    · intro h
      exact ((eisensteinFramePair_eq_iff _ _).mp (congrArg Subtype.val h)).resolve_right
        (eisensteinClass_not_neg_of_residue_one _ _
          (eisensteinOneModThree_residue _ (eisensteinTriadUnit_oneModThree r e) 0)
          (eisensteinOneModThree_residue _ (eisensteinTriadUnit_oneModThree s f) 0))
    · intro h
      exact Subtype.ext (congrArg eisensteinFramePair h)
  rw [he,eisensteinTriadUnit_class_iff,and_assoc]

end Atlas.Conway
