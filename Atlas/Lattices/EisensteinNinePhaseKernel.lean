import Atlas.Lattices.EisensteinThetaClassResidue
import Atlas.Lattices.EisensteinPhases
import Atlas.Codes.TernarySupportedHexad

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

/-- The same-class phase stabilizer for the norm-nine/hexad pattern consists
only of global phases. The hypotheses specify the actual normalized coordinates. -/
theorem eisensteinNine_phase_class_kernel (c : TernarySixWords)
    (u : EisensteinCoordinates) (hu : eisensteinTheta • u ∈ eisensteinLeechModule)
    (hc : eisensteinWordResidue u=c.val.val) (j : Fin 12)
    (hj : j ∉ ternarySupport c.val.val) (a : Eisensteinˣ)
    (huj : u j=eisensteinTheta*(a : Eisenstein))
    (hz : ∀ i, i ∉ ternarySupport c.val.val → i≠j → u i=0)
    (t : ternaryGolay)
    (hclass : eisensteinClass ⟨eisensteinTheta • u,hu⟩ =
      eisensteinClass ⟨eisensteinDiagonal t.val (eisensteinTheta • u),eisensteinDiagonal_mem t hu⟩) :
    ∃ b : ZMod 3,∀ i,t.val i=b := by
  let v : EisensteinCoordinates := fun i => eisensteinPhaseCorrection (t.val i)*u i
  have hdiff : (eisensteinTheta • u)-eisensteinDiagonal t.val (eisensteinTheta • u) =
      (3 : Eisenstein) • v := by
    funext i
    change eisensteinTheta*u i-eisensteinPhase (t.val i)*(eisensteinTheta*u i)=3*v i
    rw [eisensteinPhase_correction]
    dsimp [v]
    linear_combination -(eisensteinPhaseCorrection (t.val i)*u i)*eisensteinTheta_sq
  obtain ⟨hcode,hsum⟩ := (eisensteinClass_difference_three_iff _ _ v hdiff).mp hclass
  have hprod : (fun i => c.val.val i*t.val i) ∈ ternaryGolay := by
    have h := ternaryGolay.neg_mem hcode
    convert h using 1
    funext i
    have hi := congrFun hc i
    change eisensteinResidue (u i)=c.val.val i at hi
    simp [v,eisensteinWordResidue,hi,mul_comm]
  obtain ⟨b,hb⟩ := ternaryGolay_hexad_multiplier_constant c t.val hprod
  have he (i : Fin 12) : v i = eisensteinPhaseCorrection b*u i+
      if i=j then eisensteinTheta*(a : Eisenstein)*
        (eisensteinPhaseCorrection (t.val j)-eisensteinPhaseCorrection b) else 0 := by
    by_cases hij : i=j
    · subst i; simp only [v,ite_true,huj]; ring
    · by_cases hi : i ∈ ternarySupport c.val.val
      · simp [v,hb i hi,hij]
      · simp [v,hz i hi hij,hij]
  have hs : ∑ i,v i = eisensteinPhaseCorrection b*(∑ i,u i)+
      eisensteinTheta*(a : Eisenstein)*(eisensteinPhaseCorrection (t.val j)-eisensteinPhaseCorrection b) := by
    simp_rw [he]
    simp [Finset.sum_add_distrib,← Finset.mul_sum]
  have huSum := ((eisensteinLeechModule_theta_iff u).mp hu).2
  have hd : (3 : Eisenstein) ∣ eisensteinTheta*((a : Eisenstein)*
      (eisensteinPhaseCorrection (t.val j)-eisensteinPhaseCorrection b)) := by
    have h := dvd_sub hsum (huSum.mul_left (eisensteinPhaseCorrection b))
    rw [hs] at h
    simpa [mul_assoc] using h
  have hdTheta := (eisenstein_three_dvd_theta_iff _).mp hd
  have hr := (eisensteinResidue_eq_zero _).mpr hdTheta
  simp only [map_mul,map_sub,eisensteinPhaseCorrection_residue] at hr
  have ha : eisensteinResidue (a : Eisenstein) ≠ 0 :=
    (a.isUnit.map eisensteinResidue).ne_zero
  have hjb : t.val j=b := by
    have h := (mul_eq_zero.mp hr).resolve_left ha
    linear_combination -h
  exact ⟨b,ternaryGolay_constant_hexad_point c t b hb j hj hjb⟩

end Atlas.Lattices
