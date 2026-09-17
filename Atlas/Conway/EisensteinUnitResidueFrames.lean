import Atlas.Conway.EisensteinHeavyUnitOrbit

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

/-- Coordinatewise normalization modulo the rational prime three. -/
def EisensteinOneModThree (x : EisensteinLattice) : Prop :=
  ∃ a : EisensteinCoordinates, ∀ j, x.val j=1+3*a j

def eisensteinCodePhaseShell (t : ternaryGolay) (x : EisensteinShell 6) : EisensteinShell 6 :=
  eisensteinShellAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) 6 x

theorem eisensteinCodePhaseShell_apply (t : ternaryGolay) (x : EisensteinShell 6) (j : Fin 12) :
    (eisensteinCodePhaseShell t x).val.val j = eisensteinPhase (t.val j)*x.val.val j :=
  eisensteinIntegralAction_phase_apply t x.val j

theorem eisensteinCodePhaseShell_strip (t : ternaryGolay) (x : EisensteinShell 6) :
    eisensteinIntegralAction (eisensteinPhaseIsometries (Multiplicative.ofAdd (-t)))
      (eisensteinCodePhaseShell t x).val = x.val := by
  apply Subtype.ext
  funext j
  rw [eisensteinIntegralAction_phase_apply,eisensteinCodePhaseShell_apply]
  change eisensteinPhase (-t.val j)*(eisensteinPhase (t.val j)*x.val.val j) = _
  rw [← mul_assoc,eisensteinPhase_neg_mul,one_mul]

theorem eisensteinCodePhaseShell_class_of_constants (x : EisensteinShell 6)
    (t s : ternaryGolay) (h : t-s ∈ ternaryConstants) :
    eisensteinClass (eisensteinCodePhaseShell t x).val =
      eisensteinClass (eisensteinCodePhaseShell s x).val := by
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
  have he : (eisensteinCodePhaseShell t x).val = eisensteinPhase c • (eisensteinCodePhaseShell s x).val := by
    apply Subtype.ext
    funext j
    have hj := congrFun (congrArg Subtype.val hc) j
    change c*1=t.val j-s.val j at hj
    have ht : t.val j=c+s.val j := by linear_combination -hj
    change (eisensteinCodePhaseShell t x).val.val j =
      eisensteinPhase c*(eisensteinCodePhaseShell s x).val.val j
    rw [eisensteinCodePhaseShell_apply,eisensteinCodePhaseShell_apply,ht,eisensteinPhase_add,mul_assoc]
  rw [he,eisensteinClass_phase]

def eisensteinOneModThreeCorrection (a : EisensteinCoordinates) (t : TernaryWord) : EisensteinCoordinates :=
  fun j => eisensteinPhaseCorrection (t j)-eisensteinTheta*eisensteinPhase (t j)*a j

theorem eisensteinOneModThree_phase_correction (x : EisensteinShell 6) (a : EisensteinCoordinates)
    (ha : ∀ j, x.val.val j=1+3*a j) (t : ternaryGolay) (j : Fin 12) :
    (eisensteinCodePhaseShell t x).val.val j =
      1+eisensteinTheta*eisensteinOneModThreeCorrection a t.val j := by
  rw [eisensteinCodePhaseShell_apply,ha]
  unfold eisensteinOneModThreeCorrection
  linear_combination eisensteinPhase (t.val j)*a j*eisensteinTheta_sq + eisensteinPhase_correction (t.val j)

theorem eisensteinOneModThreeCorrection_residue (a : EisensteinCoordinates) (t : TernaryWord) (j : Fin 12) :
    eisensteinResidue (eisensteinOneModThreeCorrection a t j) = -t j := by
  simp [eisensteinOneModThreeCorrection,show eisensteinResidue eisensteinTheta=0 by decide +kernel]

theorem eisensteinOneModThree_phase_residue (x : EisensteinShell 6)
    (hx : EisensteinOneModThree x.val) (t : ternaryGolay) (j : Fin 12) :
    eisensteinResidue ((eisensteinCodePhaseShell t x).val.val j) = 1 := by
  obtain ⟨a,ha⟩ := hx
  rw [eisensteinOneModThree_phase_correction x a ha]
  simp [show eisensteinResidue eisensteinTheta=0 by decide +kernel]

theorem eisensteinOneModThree_phase_constants (x y : EisensteinShell 6)
    (hx : EisensteinOneModThree x.val) (hy : EisensteinOneModThree y.val) (t s : ternaryGolay)
    (h : eisensteinClass (eisensteinCodePhaseShell t x).val =
      eisensteinClass (eisensteinCodePhaseShell s y).val) : t-s ∈ ternaryConstants := by
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  obtain ⟨w,hw⟩ := (Submodule.Quotient.eq _).mp h
  have he (j : Fin 12) : w.val j =
      eisensteinOneModThreeCorrection a t.val j-eisensteinOneModThreeCorrection b s.val j := by
    apply eisenstein_theta_cancel
    have hj := congrFun (congrArg Subtype.val hw) j
    change eisensteinTheta*w.val j =
      (eisensteinCodePhaseShell t x).val.val j-(eisensteinCodePhaseShell s y).val.val j at hj
    rw [eisensteinOneModThree_phase_correction x a ha,eisensteinOneModThree_phase_correction y b hb] at hj
    linear_combination hj
  obtain ⟨m,hm⟩ := w.property
  have hr (j : Fin 12) : -t.val j+s.val j=eisensteinResidue m := by
    have hh := eisensteinCongruence_residue w.val m hm j
    rw [he,map_sub,eisensteinOneModThreeCorrection_residue,eisensteinOneModThreeCorrection_residue] at hh
    simpa using hh
  apply Submodule.mem_span_singleton.mpr
  refine ⟨t.val 0-s.val 0,?_⟩
  apply Subtype.ext
  funext j
  change (t.val 0-s.val 0)*1=t.val j-s.val j
  linear_combination -(hr 0).trans (hr j).symm


theorem eisensteinClass_not_neg_of_residue_one (x y : EisensteinLattice)
    (hx : eisensteinResidue (x.val 0)=1) (hy : eisensteinResidue (y.val 0)=1) :
    eisensteinClass x ≠ -eisensteinClass y := by
  intro h
  rw [← map_neg] at h
  obtain ⟨w,hw⟩ := (Submodule.Quotient.eq _).mp h
  have hh := congrArg eisensteinResidue (congrFun (congrArg Subtype.val hw) 0)
  change eisensteinResidue (eisensteinTheta*w.val 0) = eisensteinResidue (x.val 0- -y.val 0) at hh
  simp only [map_mul,map_sub,map_neg,hx,hy,
    show eisensteinResidue eisensteinTheta=0 by decide +kernel,zero_mul] at hh
  exact (by decide : (0 : ZMod 3)≠1 - -1) hh

theorem eisensteinOneModThree_residue (x : EisensteinLattice) (hx : EisensteinOneModThree x) (j : Fin 12) :
    eisensteinResidue (x.val j)=1 := by
  obtain ⟨a,ha⟩ := hx
  rw [ha]
  simp [show eisensteinResidue (3 : Eisenstein)=0 by decide +kernel]

/-- On normalized scalar vectors, the phase quotient and the unphased frame
are independent invariants. -/
theorem eisensteinOneModThree_frame_phase_iff (x y : EisensteinShell 6)
    (hx : EisensteinOneModThree x.val) (hy : EisensteinOneModThree y.val) (t s : ternaryGolay) :
    eisensteinFrameOfVector (eisensteinCodePhaseShell t x) =
      eisensteinFrameOfVector (eisensteinCodePhaseShell s y) ↔
    eisensteinFrameOfVector x=eisensteinFrameOfVector y ∧ t-s ∈ ternaryConstants := by
  constructor
  · intro h
    have hh := (eisensteinFramePair_eq_iff _ _).mp (congrArg Subtype.val h)
    have he := hh.resolve_right (eisensteinClass_not_neg_of_residue_one _ _
      (eisensteinOneModThree_phase_residue x hx t 0) (eisensteinOneModThree_phase_residue y hy s 0))
    have hc := eisensteinOneModThree_phase_constants x y hx hy t s he
    refine ⟨?_,hc⟩
    rw [eisensteinCodePhaseShell_class_of_constants x t s hc] at he
    have hs := congrArg (eisensteinClassAction (eisensteinPhaseIsometries (Multiplicative.ofAdd (-s)))) he
    rw [eisensteinClassAction_mk,eisensteinClassAction_mk,
      eisensteinCodePhaseShell_strip,eisensteinCodePhaseShell_strip] at hs
    exact Subtype.ext (congrArg eisensteinFramePair hs)
  · rintro ⟨h,hc⟩
    have hh := (eisensteinFramePair_eq_iff _ _).mp (congrArg Subtype.val h)
    have he := hh.resolve_right (eisensteinClass_not_neg_of_residue_one _ _
      (eisensteinOneModThree_residue x.val hx 0) (eisensteinOneModThree_residue y.val hy 0))
    apply Subtype.ext
    apply congrArg eisensteinFramePair
    rw [eisensteinCodePhaseShell_class_of_constants x t s hc]
    exact congrArg (eisensteinClassAction (eisensteinPhaseIsometries (Multiplicative.ofAdd s))) he

/-- Class equality for normalized vectors reduces to the actual ternary
syndrome and one integral sum congruence. -/
theorem eisensteinOneModThree_class_iff (x y : EisensteinLattice) (a b : EisensteinCoordinates)
    (ha : ∀ j, x.val j=1+3*a j) (hb : ∀ j, y.val j=1+3*b j) :
    eisensteinClass x=eisensteinClass y ↔
      eisensteinWordResidue (a-b) ∈ ternaryGolay ∧ (3 : Eisenstein) ∣ ∑ j, (a-b) j := by
  have he (w : EisensteinLattice) (hw : eisensteinThetaEnd w=x-y) :
      w.val=eisensteinTheta • (-(a-b)) := by
    funext j
    apply eisenstein_theta_cancel
    have hj := congrFun (congrArg Subtype.val hw) j
    change eisensteinTheta*w.val j=x.val j-y.val j at hj
    rw [ha,hb] at hj
    change eisensteinTheta*w.val j=eisensteinTheta*(eisensteinTheta*(-(a j-b j)))
    linear_combination hj+(a j-b j)*eisensteinTheta_sq
  constructor
  · intro h
    obtain ⟨w,hw⟩ := (Submodule.Quotient.eq _).mp h
    have hwv := he w hw
    have hc := eisensteinLeechModule_theta_code (-(a-b)) (hwv ▸ w.property)
    have hres : eisensteinWordResidue (-(a-b)) = -eisensteinWordResidue (a-b) := by
      funext j; exact map_neg eisensteinResidue _
    rw [hres] at hc
    refine ⟨ternaryGolay.neg_mem_iff.mp hc,?_⟩
    have hm := eisensteinLeechModule_common_lift w.val w.property 0 (fun j => by
      rw [hwv]
      simp [show eisensteinResidue eisensteinTheta=0 by decide +kernel])
    obtain ⟨_,_,_,d,hd⟩ := hm
    have hsum : ∑ j, w.val j = -eisensteinTheta*(∑ j,(a-b) j) := by
      rw [hwv]
      simp only [Pi.smul_apply,smul_eq_mul,Pi.neg_apply,mul_neg,Finset.sum_neg_distrib,← Finset.mul_sum,neg_mul]
    rw [hsum,mul_zero,add_zero] at hd
    refine ⟨-d,?_⟩
    apply eisenstein_theta_cancel
    linear_combination -hd
  · rintro ⟨hc,⟨d,hd⟩⟩
    let w : EisensteinCoordinates := eisensteinTheta • (-(a-b))
    have hw : w ∈ eisensteinLeechModule := by
      refine ⟨0,-(a-b),fun j => by simp [w]; ring,?_,?_⟩
      · have hh := ternaryGolay.neg_mem hc
        convert hh using 1
        funext j; exact map_neg eisensteinResidue _
      · refine ⟨-d,?_⟩
        change (∑ j, eisensteinTheta*(-(a-b) j))+3*0 = 3*eisensteinTheta*(-d)
        simp only [mul_zero,add_zero,Pi.neg_apply,mul_neg,Finset.sum_neg_distrib,← Finset.mul_sum]
        rw [hd]
        ring
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨⟨w,hw⟩,?_⟩
    apply Subtype.ext
    funext j
    change eisensteinTheta*(eisensteinTheta*(-(a j-b j)))=x.val j-y.val j
    rw [ha,hb]
    linear_combination -(a j-b j)*eisensteinTheta_sq


/-- The code congruence is automatic for coordinates congruent to one modulo three;
only the displayed scalar sum remains. -/
theorem eisensteinOneModThree_mem (a : EisensteinCoordinates)
    (ha : eisensteinTheta ∣ 5+∑ j, a j) :
    (fun j => 1+3*a j) ∈ eisensteinLeechModule := by
  refine ⟨1,-eisensteinTheta • a,?_,?_,?_⟩
  · intro j
    change 1+3*a j=1+eisensteinTheta*(-eisensteinTheta*a j)
    linear_combination a j*eisensteinTheta_sq
  · have he : eisensteinWordResidue (-eisensteinTheta • a)=0 := by
      funext j
      simp [eisensteinWordResidue,Pi.smul_apply,
        show eisensteinResidue eisensteinTheta=0 by decide +kernel]
    rw [he]
    exact ternaryGolay.zero_mem
  · obtain ⟨d,hd⟩ := ha
    refine ⟨d,?_⟩
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    linear_combination 3*hd

end Atlas.Conway
