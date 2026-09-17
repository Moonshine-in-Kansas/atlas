import Atlas.Conway.EisensteinHeavyUnitOrbit

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

/-- The norm-profile condition is imposed on the actual lattice vector. -/
def EisensteinHeavyUnitPattern (x : EisensteinShell 6) : Prop :=
  ∃ i : Fin 12, (x.val.val i).norm=16 ∧ ∀ j, j≠i → (x.val.val j).norm=1

theorem eisensteinHeavyUnitPhase_necessary (i : Fin 12) (t : TernaryWord)
    (ht : eisensteinDiagonal t (eisensteinHeavyUnitCoordinates i) ∈ eisensteinLeechModule) :
    t ∈ ternaryGolay := by
  have hu (j : Fin 12) : eisensteinDiagonal t (eisensteinHeavyUnitCoordinates i) j =
      1+eisensteinTheta*eisensteinHeavyPhaseCorrection i t j := by
    change eisensteinPhase (t j)*(1+3*(Pi.single i (1 : Eisenstein) : EisensteinCoordinates) j) =
      1+eisensteinTheta*(eisensteinPhaseCorrection (t j)-
        eisensteinTheta*eisensteinPhase (t j)*(Pi.single i (1 : Eisenstein) : EisensteinCoordinates) j)
    linear_combination eisensteinPhase (t j)*(Pi.single i (1 : Eisenstein) : EisensteinCoordinates) j*eisensteinTheta_sq +
      eisensteinPhase_correction (t j)
  have hc := eisensteinLeechModule_code_of_witness _ ht 1 (eisensteinHeavyPhaseCorrection i t) hu
  have he : eisensteinWordResidue (eisensteinHeavyPhaseCorrection i t) = -t := by
    funext j
    exact eisensteinHeavyPhaseCorrection_residue i t j
  rw [he] at hc
  exact (ternaryGolay.neg_mem_iff).mp hc

theorem eisensteinHeavyUnitPattern_normalized (x : EisensteinShell 6)
    (hx : EisensteinHeavyUnitPattern x) (hr : ∀ j, eisensteinResidue (x.val.val j)=1) :
    ∃ i t, x=eisensteinHeavyPhaseVector i t := by
  obtain ⟨i,hi,hrest⟩ := hx
  have hu (j : Fin 12) : ∃ u : Eisensteinˣ,
      x.val.val j=eisensteinHeavyUnitCoordinates i j*(u : Eisenstein) := by
    by_cases hj : j=i
    · subst j
      obtain ⟨r,hrr,u,he⟩ := eisenstein_small_norm_unit (x.val.val i) (by omega)
      have hr4 : r=4 := by simpa [eisensteinSmallNormRepresentatives,hi] using hrr
      refine ⟨u,?_⟩
      rw [he,hr4]
      norm_num [eisensteinHeavyUnitCoordinates]
    · obtain ⟨u,he⟩ := (eisenstein_isUnit_iff _).mpr (hrest j hj)
      refine ⟨u,?_⟩
      simp [eisensteinHeavyUnitCoordinates,Pi.single_apply,hj,he]
  choose u hu using hu
  have hphase (j : Fin 12) : ∃ a : ZMod 3, (u j : Eisenstein)=eisensteinPhase a := by
    apply eisensteinUnit_residue_one_phase _ (u j).isUnit
    have hh := hr j
    rw [hu j,map_mul] at hh
    have hb : eisensteinResidue (eisensteinHeavyUnitCoordinates i j)=1 := by
      simp [eisensteinHeavyUnitCoordinates,show eisensteinResidue (3 : Eisenstein)=0 by decide +kernel]
    simpa [hb] using hh
  choose t ht using hphase
  have he : x.val.val = eisensteinDiagonal t (eisensteinHeavyUnitCoordinates i) := by
    funext j
    rw [hu j,ht j]
    exact mul_comm _ _
  have hc : t ∈ ternaryGolay := eisensteinHeavyUnitPhase_necessary i t (he ▸ x.val.property)
  refine ⟨i,⟨t,hc⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext j
  rw [eisensteinHeavyPhaseVector_apply]
  exact congrFun he j


theorem eisensteinHeavyPhase_pattern (i : Fin 12) (t : ternaryGolay) :
    EisensteinHeavyUnitPattern (eisensteinHeavyPhaseVector i t) := by
  have hn (j : Fin 12) : ((eisensteinHeavyPhaseVector i t).val.val j).norm =
      (eisensteinHeavyUnitCoordinates i j).norm := by
    rw [eisensteinHeavyPhaseVector_apply,map_mul]
    have hp : (eisensteinPhase (t.val j)).norm=1 :=
      (eisenstein_isUnit_iff _).mp (eisensteinPhaseUnit (t.val j)).isUnit
    rw [hp,one_mul]
  refine ⟨i,?_,?_⟩
  · rw [hn]
    simp [eisensteinHeavyUnitCoordinates,show (1+3 : Eisenstein).norm=16 by decide +kernel]
  · intro j hj
    rw [hn]
    simp [eisensteinHeavyUnitCoordinates,Pi.single_apply,hj]

theorem eisenstein_scalar_norm_neg (z : Eisenstein) : (-z).norm=z.norm := by
  rw [eisenstein_norm,eisenstein_norm]
  simp

theorem eisensteinHeavyUnitPattern_complete (x : EisensteinShell 6)
    (hx : EisensteinHeavyUnitPattern x) :
    eisensteinFrameOfVector x ∈ eisensteinHeavyUnitFrames := by
  have hnz : eisensteinResidue (x.val.val 0)≠0 := by
    intro h
    have hd := (eisensteinResidue_zero_iff_norm _).mp h
    obtain ⟨i,hi,hr⟩ := hx
    by_cases h0 : (0 : Fin 12)=i
    · rw [h0,hi] at hd
      norm_num at hd
    · rw [hr 0 h0] at hd
      norm_num at hd
  obtain ⟨m,hm⟩ := x.val.property
  have hmn : eisensteinResidue m≠0 := fun h => hnz ((eisensteinCongruence_residue _ m hm 0).trans h)
  have hcases : ∀ a : ZMod 3, a≠0 → a=1 ∨ a= -1 := by decide
  rcases hcases _ hmn with hm1|hm1
  · obtain ⟨i,t,rfl⟩ := eisensteinHeavyUnitPattern_normalized x hx
      (fun j => (eisensteinCongruence_residue _ m hm j).trans hm1)
    exact ⟨(i,t),rfl⟩
  · let y : EisensteinShell 6 := ⟨-x.val,(eisensteinNorm_neg x.val).trans x.property⟩
    have hy : EisensteinHeavyUnitPattern y := by
      obtain ⟨i,hi,hr⟩ := hx
      refine ⟨i,?_,?_⟩
      · change (-(x.val.val i)).norm=16
        rw [eisenstein_scalar_norm_neg,hi]
      · intro j hj
        change (-(x.val.val j)).norm=1
        rw [eisenstein_scalar_norm_neg,hr j hj]
    have hyr (j : Fin 12) : eisensteinResidue (y.val.val j)=1 := by
      change eisensteinResidue (-x.val.val j)=1
      rw [map_neg,eisensteinCongruence_residue _ m hm j,hm1,neg_neg]
    obtain ⟨i,t,ht⟩ := eisensteinHeavyUnitPattern_normalized y hy hyr
    have hf : eisensteinFrameOfVector x = eisensteinFrameOfVector y := by
      apply Subtype.ext
      change eisensteinFramePair (eisensteinClass x.val) = eisensteinFramePair (eisensteinClass (-x.val))
      rw [map_neg,eisensteinFramePair_neg]
    rw [hf,ht]
    exact ⟨(i,t),rfl⟩

/-- Intrinsic characterization of the 2916-orbit: exactly the frames containing
an actual lattice vector with scalar norm profile (16,1^11). -/
theorem eisensteinHeavyUnitFrames_iff (F : EisensteinFrame) :
    F ∈ eisensteinHeavyUnitFrames ↔
      ∃ x : EisensteinShell 6, EisensteinHeavyUnitPattern x ∧ eisensteinFrameOfVector x=F := by
  constructor
  · rintro ⟨⟨i,t⟩,rfl⟩
    exact ⟨eisensteinHeavyPhaseVector i t,eisensteinHeavyPhase_pattern i t,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact eisensteinHeavyUnitPattern_complete x hx

end Atlas.Conway
