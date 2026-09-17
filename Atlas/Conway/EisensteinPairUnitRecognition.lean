import Atlas.Conway.EisensteinPairUnitOrbit
import Atlas.Conway.EisensteinHeavyUnitRecognition
import Atlas.Lattices.EisensteinResidueUnitForms

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

/-- Necessity of the actual code phases for any scalar-normalized baseline. -/
theorem eisensteinOneModThree_phase_necessary (z a : EisensteinCoordinates)
    (ha : ∀ j, z j=1+3*a j) (t : TernaryWord)
    (ht : eisensteinDiagonal t z ∈ eisensteinLeechModule) : t ∈ ternaryGolay := by
  have hu (j : Fin 12) : eisensteinDiagonal t z j =
      1+eisensteinTheta*eisensteinOneModThreeCorrection a t j := by
    change eisensteinPhase (t j)*z j = _
    rw [ha]
    unfold eisensteinOneModThreeCorrection
    linear_combination eisensteinPhase (t j)*a j*eisensteinTheta_sq + eisensteinPhase_correction (t j)
  have hc := eisensteinLeechModule_code_of_witness _ ht 1 (eisensteinOneModThreeCorrection a t) hu
  have he : eisensteinWordResidue (eisensteinOneModThreeCorrection a t) = -t := by
    funext j; exact eisensteinOneModThreeCorrection_residue a t j
  rw [he] at hc
  exact ternaryGolay.neg_mem_iff.mp hc

def EisensteinPairUnitPattern (x : EisensteinShell 6) : Prop :=
  ∃ p : EisensteinOrderedPair, (x.val.val p.val.1).norm=13 ∧
    (x.val.val p.val.2).norm=4 ∧ ∀ j, j≠p.val.1 → j≠p.val.2 → (x.val.val j).norm=1

theorem eisensteinPairUnitPattern_normalized (x : EisensteinShell 6)
    (hx : EisensteinPairUnitPattern x) (hr : ∀ j, eisensteinResidue (x.val.val j)=1) :
    ∃ b p t, x=eisensteinCodePhaseShell t (eisensteinPairUnitVector b p) := by
  obtain ⟨p,h13,h4,hrest⟩ := hx
  obtain ⟨r,hrr,c,hc⟩ := eisensteinResidueOne_normalize (x.val.val p.val.1) (by omega) (hr _)
  have hrc : r=1-3*eisensteinOmega ∨ r=4+3*eisensteinOmega := by
    simpa [eisensteinResidueOneForms,h13] using hrr
  have hb : ∃ b : Bool, r=1+3*eisensteinPairChirality b := by
    rcases hrc with rfl|rfl
    · refine ⟨false,?_⟩
      simp only [eisensteinPairChirality,Bool.false_eq_true,if_false,if_true]
      ring
    · refine ⟨true,?_⟩
      simp only [eisensteinPairChirality,Bool.false_eq_true,if_false,if_true]
      ring
  obtain ⟨b,hb⟩ := hb
  have hp (j : Fin 12) : ∃ c : ZMod 3,
      x.val.val j=eisensteinPhase c*eisensteinPairUnitCoordinates b p j := by
    by_cases hj : j=p.val.1
    · subst j
      refine ⟨c,?_⟩
      rw [hc,hb]
      simp [eisensteinPairUnitCoordinates,eisensteinPairUnitA,Pi.smul_apply,p.property]
    · by_cases hk : j=p.val.2
      · subst j
        obtain ⟨s,hs,d,hd⟩ := eisensteinResidueOne_normalize (x.val.val p.val.2) (by omega) (hr _)
        have hs' : s= -2 := by simpa [eisensteinResidueOneForms,h4] using hs
        refine ⟨d,?_⟩
        rw [hd,hs']
        simp [eisensteinPairUnitCoordinates,eisensteinPairUnitA,Pi.smul_apply,Ne.symm p.property]
        ring
      · obtain ⟨s,hs,d,hd⟩ := eisensteinResidueOne_normalize (x.val.val j) (by have hh := hrest j hj hk; omega) (hr _)
        have hs' : s=1 := by simpa [eisensteinResidueOneForms,hrest j hj hk] using hs
        refine ⟨d,?_⟩
        rw [hd,hs']
        simp [eisensteinPairUnitCoordinates,eisensteinPairUnitA,Pi.smul_apply,Pi.single_apply,hj,hk]
  choose t ht using hp
  have he : x.val.val=eisensteinDiagonal t (eisensteinPairUnitCoordinates b p) := funext ht
  have htc : t ∈ ternaryGolay := eisensteinOneModThree_phase_necessary
    (eisensteinPairUnitCoordinates b p) (eisensteinPairUnitA b p) (fun _ => rfl) t (he ▸ x.val.property)
  refine ⟨b,p,⟨t,htc⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext j
  rw [eisensteinCodePhaseShell_apply]
  exact ht j


theorem eisensteinPairUnit_phase_pattern (b : Bool) (p : EisensteinOrderedPair) (t : ternaryGolay) :
    EisensteinPairUnitPattern (eisensteinCodePhaseShell t (eisensteinPairUnitVector b p)) := by
  have hn (j : Fin 12) : ((eisensteinCodePhaseShell t (eisensteinPairUnitVector b p)).val.val j).norm =
      (eisensteinPairUnitCoordinates b p j).norm := by
    rw [eisensteinCodePhaseShell_apply,map_mul]
    have hp : (eisensteinPhase (t.val j)).norm=1 :=
      (eisenstein_isUnit_iff _).mp (eisensteinPhaseUnit (t.val j)).isUnit
    rw [hp,one_mul]
    rfl
  have h13 : (1+3*eisensteinPairChirality b).norm=13 := by cases b <;> decide +kernel
  refine ⟨p,?_,?_,?_⟩
  · rw [hn]
    simp [eisensteinPairUnitCoordinates,eisensteinPairUnitA,Pi.smul_apply,p.property,h13]
  · rw [hn]
    simp [eisensteinPairUnitCoordinates,eisensteinPairUnitA,Pi.smul_apply,Ne.symm p.property,
      show (1+ -3 : Eisenstein).norm=4 by decide +kernel]
  · intro j hj hk
    rw [hn]
    simp [eisensteinPairUnitCoordinates,eisensteinPairUnitA,Pi.smul_apply,Pi.single_apply,hj,hk]

theorem eisensteinPairUnitPattern_complete (x : EisensteinShell 6)
    (hx : EisensteinPairUnitPattern x) :
    ∃ b, eisensteinFrameOfVector x ∈ eisensteinPairUnitFrames b := by
  have hnz : eisensteinResidue (x.val.val 0)≠0 := by
    intro h
    have hd := (eisensteinResidue_zero_iff_norm _).mp h
    obtain ⟨p,h13,h4,hr⟩ := hx
    by_cases hi : (0 : Fin 12)=p.val.1
    · rw [hi,h13] at hd
      norm_num at hd
    · by_cases hj : (0 : Fin 12)=p.val.2
      · rw [hj,h4] at hd
        norm_num at hd
      · rw [hr 0 hi hj] at hd
        norm_num at hd
  obtain ⟨m,hm⟩ := x.val.property
  have hmn : eisensteinResidue m≠0 := fun h => hnz ((eisensteinCongruence_residue _ m hm 0).trans h)
  have hcases : ∀ a : ZMod 3, a≠0 → a=1 ∨ a= -1 := by decide
  rcases hcases _ hmn with hm1|hm1
  · obtain ⟨b,p,t,rfl⟩ := eisensteinPairUnitPattern_normalized x hx
      (fun j => (eisensteinCongruence_residue _ m hm j).trans hm1)
    exact ⟨b,⟨(p,t),rfl⟩⟩
  · let y : EisensteinShell 6 := ⟨-x.val,(eisensteinNorm_neg x.val).trans x.property⟩
    have hy : EisensteinPairUnitPattern y := by
      obtain ⟨p,h13,h4,hr⟩ := hx
      refine ⟨p,?_,?_,?_⟩
      · change (-(x.val.val p.val.1)).norm=13
        rw [eisenstein_scalar_norm_neg,h13]
      · change (-(x.val.val p.val.2)).norm=4
        rw [eisenstein_scalar_norm_neg,h4]
      · intro j hj hk
        change (-(x.val.val j)).norm=1
        rw [eisenstein_scalar_norm_neg,hr j hj hk]
    have hyr (j : Fin 12) : eisensteinResidue (y.val.val j)=1 := by
      change eisensteinResidue (-x.val.val j)=1
      rw [map_neg,eisensteinCongruence_residue _ m hm j,hm1,neg_neg]
    obtain ⟨b,p,t,ht⟩ := eisensteinPairUnitPattern_normalized y hy hyr
    have hf : eisensteinFrameOfVector x=eisensteinFrameOfVector y := by
      apply Subtype.ext
      change eisensteinFramePair (eisensteinClass x.val)=eisensteinFramePair (eisensteinClass (-x.val))
      rw [map_neg,eisensteinFramePair_neg]
    rw [hf,ht]
    exact ⟨b,⟨(p,t),rfl⟩⟩

/-- The two disjoint chirality orbits are exactly the frames carrying an actual
norm-six vector of scalar norm profile (13,4,1^10). -/
theorem eisensteinPairUnitFrames_iff (F : EisensteinFrame) :
    (∃ b, F ∈ eisensteinPairUnitFrames b) ↔
      ∃ x : EisensteinShell 6, EisensteinPairUnitPattern x ∧ eisensteinFrameOfVector x=F := by
  constructor
  · rintro ⟨b,⟨⟨p,t⟩,rfl⟩⟩
    exact ⟨_,eisensteinPairUnit_phase_pattern b p t,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact eisensteinPairUnitPattern_complete x hx

end Atlas.Conway
