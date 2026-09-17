import Atlas.Conway.EisensteinUnitResidueSyndrome
import Atlas.Conway.EisensteinUnitFamiliesDisjoint
import Atlas.Algebra.EisensteinModuloThree

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem eisensteinWordResidue_sub_mem (a b : EisensteinCoordinates)
    (h : ternarySyndromeClass (eisensteinWordResidue a)=ternarySyndromeClass (eisensteinWordResidue b)) :
    eisensteinWordResidue (a-b) ∈ ternaryGolay := by
  have hm := (ternarySyndromeClass_eq_iff _ _).mp h
  convert hm using 1
  ext i
  exact map_sub eisensteinResidue _ _

theorem eisensteinOneModThree_sum_residue (x : EisensteinLattice) (a : EisensteinCoordinates)
    (ha : ∀ j, x.val j=1+3*a j) : eisensteinResidue (∑ j, a j)=1 := by
  rw [map_sum]
  exact eisensteinOneModThree_affine_sum x a ha

theorem eisensteinOneModThree_frame_from_sum (x y : EisensteinShell 6)
    (a b : EisensteinCoordinates) (ha : ∀ j, x.val.val j=1+3*a j)
    (hb : ∀ j, y.val.val j=1+3*b j)
    (hc : ternarySyndromeClass (eisensteinWordResidue a)=ternarySyndromeClass (eisensteinWordResidue b))
    (hd : (3 : Eisenstein) ∣ (∑ j, a j)-(∑ j, b j)) :
    eisensteinFrameOfVector x=eisensteinFrameOfVector y := by
  apply Subtype.ext
  apply congrArg eisensteinFramePair
  apply (eisensteinOneModThree_class_iff x.val y.val a b ha hb).mpr
  exact ⟨eisensteinWordResidue_sub_mem a b hc,by simpa only [Pi.sub_apply,Finset.sum_sub_distrib] using hd⟩

theorem eisensteinOneModThree_singleton_short_excluded (x : EisensteinShell 6)
    (a : EisensteinCoordinates) (ha : ∀ j, x.val.val j=1+3*a j) (i : Fin 12)
    (hc : ternarySyndromeClass (eisensteinWordResidue a)=ternarySyndromeClass (Pi.single i 1))
    (b : Bool) : ¬ (3 : Eisenstein) ∣ (∑ j, a j)-eisensteinShortSingletonCorrection b := by
  let d : EisensteinCoordinates := Pi.single i (eisensteinShortSingletonCorrection b)
  have hd : eisensteinWordResidue d=Pi.single i 1 := by
    ext j
    by_cases h : j=i <;> simp [d,eisensteinWordResidue,Pi.single_apply,eisensteinShortSingletonCorrection_residue,h]
  have hcode : eisensteinWordResidue (a-d) ∈ ternaryGolay :=
    eisensteinWordResidue_sub_mem a d (by rw [hd]; exact hc)
  have hh := eisensteinOneModThree_short_excluded x
    ⟨eisensteinShortSingletonLattice i b,eisensteinShortSingleton_norm i b⟩ a d ha (fun _ => rfl) hcode
  simpa [Pi.sub_apply,Finset.sum_sub_distrib,d] using hh

theorem eisensteinOneModThree_singleton_frame (x : EisensteinShell 6)
    (a : EisensteinCoordinates) (ha : ∀ j, x.val.val j=1+3*a j) (i : Fin 12)
    (hc : ternarySyndromeClass (eisensteinWordResidue a)=ternarySyndromeClass (Pi.single i 1)) :
    eisensteinFrameOfVector x=eisensteinFrameOfVector (eisensteinHeavyUnitVector i) := by
  have hs := eisenstein_residue_one_mod_three (∑ j, a j) (eisensteinOneModThree_sum_residue x.val a ha)
  rcases hs with hs|hs|hs
  · apply eisensteinOneModThree_frame_from_sum x (eisensteinHeavyUnitVector i) a (Pi.single i 1) ha (fun _ => rfl)
    · rwa [eisensteinWordResidue_singleton]
    · simpa using hs
  · exact False.elim (eisensteinOneModThree_singleton_short_excluded x a ha i hc true hs)
  · apply False.elim
    apply eisensteinOneModThree_singleton_short_excluded x a ha i hc false
    convert hs using 1
    congr 1

theorem eisensteinOneModThree_pair_short_excluded (x : EisensteinShell 6)
    (a : EisensteinCoordinates) (ha : ∀ j, x.val.val j=1+3*a j) (p : EisensteinOrderedPair)
    (hc : ternarySyndromeClass (eisensteinWordResidue a)=
      (ternaryPairSyndrome ⟨eisensteinPairSupport p,eisensteinPairSupport_mem p⟩).val) :
    ¬ (3 : Eisenstein) ∣ (∑ j, a j)-1 := by
  let d : EisensteinCoordinates := -Pi.single p.val.1 1-Pi.single p.val.2 1
  have hd : eisensteinWordResidue d=ternaryPairWord (eisensteinPairSupport p) := by
    ext j
    by_cases hi : j=p.val.1 <;> by_cases hj : j=p.val.2
    · exact False.elim (p.property (hi.symm.trans hj))
    all_goals simp [d,eisensteinWordResidue,Pi.single_apply,ternaryPairWord,ternaryTriadWord,
      eisensteinPairSupport,hi,hj,p.property,Ne.symm p.property]
  have hcode : eisensteinWordResidue (a-d) ∈ ternaryGolay :=
    eisensteinWordResidue_sub_mem a d (by rw [hd]; exact hc)
  have hh := eisensteinOneModThree_short_excluded x
    ⟨eisensteinShortPairLattice p.val.1 p.val.2,eisensteinShortPair_norm _ _ p.property⟩
    a d ha (fun _ => rfl) hcode
  intro h
  apply hh
  obtain ⟨w,hw⟩ := h
  refine ⟨w+1,?_⟩
  simp only [d,Pi.sub_apply,Finset.sum_sub_distrib,Pi.neg_apply,Finset.sum_neg_distrib,
    Finset.sum_pi_single',Finset.mem_univ,if_true]
  change (∑ j, a j)-(-1-1)=3*(w+1)
  linear_combination hw

theorem eisensteinOneModThree_pair_frame (x : EisensteinShell 6)
    (a : EisensteinCoordinates) (ha : ∀ j, x.val.val j=1+3*a j) (p : EisensteinOrderedPair)
    (hc : ternarySyndromeClass (eisensteinWordResidue a)=
      (ternaryPairSyndrome ⟨eisensteinPairSupport p,eisensteinPairSupport_mem p⟩).val) :
    ∃ b : Bool, eisensteinFrameOfVector x=eisensteinFrameOfVector (eisensteinPairUnitVector b p) := by
  have hs := eisenstein_residue_one_mod_three (∑ j, a j) (eisensteinOneModThree_sum_residue x.val a ha)
  rcases hs with hs|hs|hs
  · exact False.elim (eisensteinOneModThree_pair_short_excluded x a ha p hc hs)
  · refine ⟨true,?_⟩
    apply eisensteinOneModThree_frame_from_sum x (eisensteinPairUnitVector true p) a
      (eisensteinPairUnitA true p) ha (fun _ => rfl)
    · rwa [eisensteinPairUnit_syndrome]
    · rw [eisensteinPairUnitA_sum]
      convert hs using 1 <;> simp [eisensteinPairChirality]
  · refine ⟨false,?_⟩
    apply eisensteinOneModThree_frame_from_sum x (eisensteinPairUnitVector false p) a
      (eisensteinPairUnitA false p) ha (fun _ => rfl)
    · rwa [eisensteinPairUnit_syndrome]
    · rw [eisensteinPairUnitA_sum]
      convert hs using 1 <;> simp [eisensteinPairChirality] <;> ring

theorem eisensteinTriadChirality_mod_three_exhaust (z : Eisenstein) (hz : eisensteinResidue z=1) :
    ∃ r : Fin 3, (3 : Eisenstein) ∣ z-eisensteinTriadChiralitySum r := by
  rcases eisenstein_residue_one_mod_three z hz with ⟨d,hd⟩|⟨d,hd⟩|⟨d,hd⟩
  · refine ⟨1,d+1,?_⟩
    norm_num [eisensteinTriadChiralitySum,eisensteinTriadChirality]
    linear_combination hd
  · refine ⟨0,d+1+eisensteinOmega,?_⟩
    norm_num [eisensteinTriadChiralitySum,eisensteinTriadChirality]
    linear_combination hd
  · refine ⟨2,d-eisensteinOmega,?_⟩
    norm_num [eisensteinTriadChiralitySum,eisensteinTriadChirality]
    linear_combination hd

theorem eisensteinOneModThree_triad_frame (x : EisensteinShell 6)
    (a : EisensteinCoordinates) (ha : ∀ j, x.val.val j=1+3*a j) (e : Fin 3 ↪ Fin 12)
    (hc : ternarySyndromeClass (eisensteinWordResidue a)=
      ternarySyndromeClass (ternaryOrientedWord (eisensteinEmbeddingOriented e).val)) :
    ∃ r : Fin 3, eisensteinFrameOfVector x=eisensteinFrameOfVector (eisensteinTriadUnitVector r e) := by
  obtain ⟨r,hr⟩ := eisensteinTriadChirality_mod_three_exhaust (∑ j, a j)
    (eisensteinOneModThree_sum_residue x.val a ha)
  refine ⟨r,?_⟩
  apply eisensteinOneModThree_frame_from_sum x (eisensteinTriadUnitVector r e) a
    (eisensteinTriadUnitA r e) ha (fun _ => rfl)
  · rwa [eisensteinTriadUnitA_residue]
  · rwa [eisensteinTriadUnitA_sum]

theorem eisensteinCodePhaseFrame_congr (t : ternaryGolay) (x y : EisensteinShell 6)
    (h : eisensteinFrameOfVector x=eisensteinFrameOfVector y) :
    eisensteinFrameOfVector (eisensteinCodePhaseShell t x)=
      eisensteinFrameOfVector (eisensteinCodePhaseShell t y) := by
  change eisensteinFrameOfVector (eisensteinShellAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) 6 x)=
    eisensteinFrameOfVector (eisensteinShellAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) 6 y)
  rw [← eisensteinFrameAction_vector,← eisensteinFrameAction_vector,h]

theorem eisensteinResidueOne_frame_exhaust (x : EisensteinShell 6)
    (hr : ∀ j, eisensteinResidue (x.val.val j)=1) :
    eisensteinFrameOfVector x ∈ eisensteinHeavyUnitFrames ∨
      (∃ b, eisensteinFrameOfVector x ∈ eisensteinPairUnitFrames b) ∨
      ∃ r, eisensteinFrameOfVector x ∈ eisensteinTriadUnitFrames r := by
  obtain ⟨t,y,a,rfl,ha⟩ := eisensteinUnitResidue_normalize x hr
  let c := eisensteinOneModThreeSyndrome y.val a ha
  have hc : c ∈ (ternarySingletonSyndromes ∪ ternaryPairSyndromes) ∪ ternaryOrientedSyndromes := by
    rw [ternarySyndrome_partition]
    exact Finset.mem_univ _
  rcases Finset.mem_union.mp hc with hc|hc
  · rcases Finset.mem_union.mp hc with hc|hc
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hc
      have hh := eisensteinOneModThree_singleton_frame y a ha i (congrArg Subtype.val hi.symm)
      left
      exact ⟨(i,t),(eisensteinCodePhaseFrame_congr t y (eisensteinHeavyUnitVector i) hh).symm⟩
    · obtain ⟨S,_,hS⟩ := Finset.mem_image.mp hc
      let p := eisensteinPairRepresentative S
      have hp : (⟨eisensteinPairSupport p,eisensteinPairSupport_mem p⟩ : TernaryPair)=S :=
        Subtype.ext (eisensteinPairRepresentative_support S)
      obtain ⟨b,hb⟩ := eisensteinOneModThree_pair_frame y a ha p (by
        rw [hp]; exact congrArg Subtype.val hS.symm)
      right; left
      exact ⟨b,(p,t),(eisensteinCodePhaseFrame_congr t y (eisensteinPairUnitVector b p) hb).symm⟩
  · obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hc
    obtain ⟨e,he,hi⟩ := ternaryOriented_embedding p
    have heq : eisensteinEmbeddingOriented e=p := Subtype.ext (Prod.ext he hi)
    obtain ⟨r,hr⟩ := eisensteinOneModThree_triad_frame y a ha e (by
      rw [heq]; exact congrArg Subtype.val hp.symm)
    right; right
    exact ⟨r,(e,t),(eisensteinCodePhaseFrame_congr t y (eisensteinTriadUnitVector r e) hr).symm⟩

/-- The six constructed unit-residue families exhaust every intrinsic frame
represented by a vector with nonzero common theta residue. -/
theorem eisensteinNonzeroResidue_frame_exhaust (x : EisensteinShell 6)
    (hx : eisensteinResidue (x.val.val 0)≠0) :
    eisensteinFrameOfVector x ∈ eisensteinHeavyUnitFrames ∨
      (∃ b, eisensteinFrameOfVector x ∈ eisensteinPairUnitFrames b) ∨
      ∃ r, eisensteinFrameOfVector x ∈ eisensteinTriadUnitFrames r := by
  obtain ⟨m,hm⟩ := x.val.property
  have hmn : eisensteinResidue m≠0 := fun h => hx ((eisensteinCongruence_residue _ m hm 0).trans h)
  have hcases : ∀ a : ZMod 3, a≠0 → a=1 ∨ a= -1 := by decide
  rcases hcases _ hmn with hm1|hm1
  · exact eisensteinResidueOne_frame_exhaust x
      (fun j => (eisensteinCongruence_residue _ m hm j).trans hm1)
  · let y : EisensteinShell 6 := ⟨-x.val,(eisensteinNorm_neg x.val).trans x.property⟩
    have hyr (j : Fin 12) : eisensteinResidue (y.val.val j)=1 := by
      change eisensteinResidue (-x.val.val j)=1
      rw [map_neg,eisensteinCongruence_residue _ m hm j,hm1,neg_neg]
    have hf : eisensteinFrameOfVector x=eisensteinFrameOfVector y := by
      apply Subtype.ext
      change eisensteinFramePair (eisensteinClass x.val)=eisensteinFramePair (eisensteinClass (-x.val))
      rw [map_neg,eisensteinFramePair_neg]
    rw [hf]
    exact eisensteinResidueOne_frame_exhaust y hyr

end Atlas.Conway
