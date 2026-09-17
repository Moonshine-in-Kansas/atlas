import Atlas.Conway.EisensteinStandardFrame
import Atlas.Algebra.EisensteinSmallNorms
import Atlas.Lattices.EisensteinNormPatterns

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The twelve marked norm-six vectors with scalar norm profile (16,1^11). -/
def eisensteinHeavyUnitCoordinates (i : Fin 12) : EisensteinCoordinates :=
  fun j => 1+3*(Pi.single i (1 : Eisenstein) : EisensteinCoordinates) j

theorem eisensteinHeavyUnit_mem (i : Fin 12) :
    eisensteinHeavyUnitCoordinates i ∈ eisensteinLeechModule := by
  refine ⟨1,-eisensteinTheta • Pi.single i 1,?_,?_,?_⟩
  · intro j
    change 1+3*(Pi.single i (1 : Eisenstein) : EisensteinCoordinates) j =
      1+eisensteinTheta*(-eisensteinTheta*(Pi.single i (1 : Eisenstein) : EisensteinCoordinates) j)
    linear_combination ((Pi.single i (1 : Eisenstein) : EisensteinCoordinates) j)*eisensteinTheta_sq
  · have he : eisensteinWordResidue (-eisensteinTheta • Pi.single i (1 : Eisenstein)) = 0 := by
      funext j
      simp [eisensteinWordResidue,Pi.smul_apply,
        show eisensteinResidue eisensteinTheta=0 by decide +kernel]
    rw [he]
    exact ternaryGolay.zero_mem
  · refine ⟨-2*eisensteinTheta,?_⟩
    simp only [eisensteinHeavyUnitCoordinates,Finset.sum_add_distrib,
      ← Finset.mul_sum,Finset.sum_pi_single',Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_one,Finset.mem_univ,ite_true]
    linear_combination 6*eisensteinTheta_sq

def eisensteinHeavyUnitLattice (i : Fin 12) : EisensteinLattice :=
  ⟨eisensteinHeavyUnitCoordinates i,eisensteinHeavyUnit_mem i⟩

theorem eisensteinHeavyUnit_norm (i : Fin 12) : eisensteinNorm (eisensteinHeavyUnitLattice i)=6 := by
  have hc (j : Fin 12) : (eisensteinHeavyUnitCoordinates i j).norm =
      1+15*(Pi.single i (1 : ℤ) : Fin 12 → ℤ) j := by
    by_cases hj : j=i <;> simp [eisensteinHeavyUnitCoordinates,Pi.single_apply,hj,show (1+3 : Eisenstein).norm=16 by decide +kernel]
  unfold eisensteinNorm
  rw [eisensteinBilinear_self_sum_norm]
  change (2/9 : ℚ)*(∑ j, (eisensteinToRational (eisensteinHeavyUnitCoordinates i j)).norm) = 6
  simp_rw [eisensteinToRational_norm,hc]
  push_cast
  norm_num [Finset.sum_add_distrib,← Finset.mul_sum,Pi.single_apply]

def eisensteinHeavyUnitVector (i : Fin 12) : EisensteinShell 6 :=
  ⟨eisensteinHeavyUnitLattice i,eisensteinHeavyUnit_norm i⟩

def eisensteinHeavyPhaseVector (i : Fin 12) (t : ternaryGolay) : EisensteinShell 6 :=
  eisensteinShellAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) 6
    (eisensteinHeavyUnitVector i)

theorem eisensteinHeavyPhaseVector_apply (i : Fin 12) (t : ternaryGolay) (j : Fin 12) :
    (eisensteinHeavyPhaseVector i t).val.val j =
      eisensteinPhase (t.val j)*eisensteinHeavyUnitCoordinates i j := by
  apply eisensteinToRational_injective
  have h := congrFun (eisensteinIntegralAction_agrees
    (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) (eisensteinHeavyUnitLattice i)) j
  exact h.trans (map_mul eisensteinToRational _ _).symm

def eisensteinHeavyUnitFrame (i : Fin 12) (t : ternaryGolay) : EisensteinFrame :=
  eisensteinFrameOfVector (eisensteinHeavyPhaseVector i t)

def eisensteinHeavyPhaseCorrection (i : Fin 12) (t : TernaryWord) : EisensteinCoordinates :=
  fun j => eisensteinPhaseCorrection (t j)-eisensteinTheta*eisensteinPhase (t j)*(Pi.single i (1 : Eisenstein) : EisensteinCoordinates) j

theorem eisensteinHeavyPhase_correction (i : Fin 12) (t : ternaryGolay) (j : Fin 12) :
    (eisensteinHeavyPhaseVector i t).val.val j =
      1+eisensteinTheta*eisensteinHeavyPhaseCorrection i t.val j := by
  rw [eisensteinHeavyPhaseVector_apply]
  change eisensteinPhase (t.val j)*(1+3*(Pi.single i (1 : Eisenstein) : EisensteinCoordinates) j) =
    1+eisensteinTheta*(eisensteinPhaseCorrection (t.val j)-
      eisensteinTheta*eisensteinPhase (t.val j)*(Pi.single i (1 : Eisenstein) : EisensteinCoordinates) j)
  linear_combination eisensteinPhase (t.val j)*(Pi.single i (1 : Eisenstein) : EisensteinCoordinates) j*eisensteinTheta_sq +
    eisensteinPhase_correction (t.val j)

theorem eisensteinHeavyPhaseCorrection_residue (i : Fin 12) (t : TernaryWord) (j : Fin 12) :
    eisensteinResidue (eisensteinHeavyPhaseCorrection i t j) = -t j := by
  simp [eisensteinHeavyPhaseCorrection,show eisensteinResidue eisensteinTheta=0 by decide +kernel]


theorem eisensteinHeavyPhase_residue (i : Fin 12) (t : ternaryGolay) (j : Fin 12) :
    eisensteinResidue ((eisensteinHeavyPhaseVector i t).val.val j) = 1 := by
  rw [eisensteinHeavyPhase_correction]
  simp [show eisensteinResidue eisensteinTheta=0 by decide +kernel]

/-- Equality of theta-classes forces the two code phase words to differ by a constant. -/
theorem eisensteinHeavyPhase_class_constants (i k : Fin 12) (t s : ternaryGolay)
    (h : eisensteinClass (eisensteinHeavyPhaseVector i t).val =
      eisensteinClass (eisensteinHeavyPhaseVector k s).val) :
    t-s ∈ ternaryConstants := by
  obtain ⟨w,hw⟩ := (Submodule.Quotient.eq _).mp h
  have he (j : Fin 12) : w.val j =
      eisensteinHeavyPhaseCorrection i t.val j-eisensteinHeavyPhaseCorrection k s.val j := by
    apply eisenstein_theta_cancel
    have hj := congrFun (congrArg Subtype.val hw) j
    change eisensteinTheta*w.val j =
      (eisensteinHeavyPhaseVector i t).val.val j-(eisensteinHeavyPhaseVector k s).val.val j at hj
    rw [eisensteinHeavyPhase_correction,eisensteinHeavyPhase_correction] at hj
    linear_combination hj
  obtain ⟨m,hm⟩ := w.property
  have hr (j : Fin 12) : -t.val j+s.val j=eisensteinResidue m := by
    have hh := eisensteinCongruence_residue w.val m hm j
    rw [he,eisensteinResidue.map_sub,eisensteinHeavyPhaseCorrection_residue,
      eisensteinHeavyPhaseCorrection_residue] at hh
    simpa using hh
  apply Submodule.mem_span_singleton.mpr
  refine ⟨t.val 0-s.val 0,?_⟩
  apply Subtype.ext
  funext j
  change (t.val 0-s.val 0)*1 = t.val j-s.val j
  have hh := (hr 0).trans (hr j).symm
  linear_combination -hh

/-- Opposite theta-classes cannot both have scalar residue one. -/
theorem eisensteinHeavyPhase_class_not_neg (i k : Fin 12) (t s : ternaryGolay) :
    eisensteinClass (eisensteinHeavyPhaseVector i t).val ≠
      -eisensteinClass (eisensteinHeavyPhaseVector k s).val := by
  intro h
  rw [← map_neg] at h
  obtain ⟨w,hw⟩ := (Submodule.Quotient.eq _).mp h
  have hh := congrArg eisensteinResidue (congrFun (congrArg Subtype.val hw) 0)
  change eisensteinResidue (eisensteinTheta*w.val 0) =
    eisensteinResidue ((eisensteinHeavyPhaseVector i t).val.val 0 -
      -(eisensteinHeavyPhaseVector k s).val.val 0) at hh
  simp only [map_mul,map_sub,map_neg,eisensteinHeavyPhase_residue,
    show eisensteinResidue eisensteinTheta=0 by decide +kernel,zero_mul] at hh
  exact (by decide : (0 : ZMod 3)≠1 - -1) hh

theorem eisensteinHeavyUnitFrame_constants (i k : Fin 12) (t s : ternaryGolay)
    (h : eisensteinHeavyUnitFrame i t = eisensteinHeavyUnitFrame k s) : t-s ∈ ternaryConstants := by
  have hh := (eisensteinFramePair_eq_iff _ _).mp (congrArg Subtype.val h)
  rcases hh with hh|hh
  · exact eisensteinHeavyPhase_class_constants i k t s hh
  · exact (eisensteinHeavyPhase_class_not_neg i k t s hh).elim


theorem eisensteinHeavyPhase_class_of_constants (i : Fin 12) (t s : ternaryGolay)
    (h : t-s ∈ ternaryConstants) :
    eisensteinClass (eisensteinHeavyPhaseVector i t).val =
      eisensteinClass (eisensteinHeavyPhaseVector i s).val := by
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
  have he : (eisensteinHeavyPhaseVector i t).val =
      eisensteinPhase c • (eisensteinHeavyPhaseVector i s).val := by
    apply Subtype.ext
    funext j
    have hj := congrFun (congrArg Subtype.val hc) j
    change c*1=t.val j-s.val j at hj
    have ht : t.val j=c+s.val j := by linear_combination -hj
    change (eisensteinHeavyPhaseVector i t).val.val j =
      eisensteinPhase c*(eisensteinHeavyPhaseVector i s).val.val j
    rw [eisensteinHeavyPhaseVector_apply,eisensteinHeavyPhaseVector_apply,ht,eisensteinPhase_add,mul_assoc]
  rw [he,eisensteinClass_phase]

theorem eisensteinIntegralAction_phase_apply (t : ternaryGolay) (x : EisensteinLattice) (j : Fin 12) :
    (eisensteinIntegralAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) x).val j =
      eisensteinPhase (t.val j)*x.val j := by
  apply eisensteinToRational_injective
  exact (congrFun (eisensteinIntegralAction_agrees
    (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) x) j).trans
      (map_mul eisensteinToRational _ _).symm

theorem eisensteinHeavyPhase_strip (i : Fin 12) (s : ternaryGolay) :
    eisensteinIntegralAction (eisensteinPhaseIsometries (Multiplicative.ofAdd (-s)))
      (eisensteinHeavyPhaseVector i s).val = eisensteinHeavyUnitLattice i := by
  apply Subtype.ext
  funext j
  rw [eisensteinIntegralAction_phase_apply,eisensteinHeavyPhaseVector_apply]
  change eisensteinPhase (-s.val j)*(eisensteinPhase (s.val j)*eisensteinHeavyUnitCoordinates i j) = _
  rw [← mul_assoc,eisensteinPhase_neg_mul,one_mul]
  rfl

theorem eisensteinHeavyUnit_class_injective :
    Function.Injective (fun i => eisensteinClass (eisensteinHeavyUnitLattice i)) := by
  intro i k h
  obtain ⟨w,hw⟩ := (Submodule.Quotient.eq _).mp h
  let v : EisensteinCoordinates := fun j => -(Pi.single i (1 : Eisenstein) : EisensteinCoordinates) j+
    (Pi.single k (1 : Eisenstein) : EisensteinCoordinates) j
  have he : w.val = eisensteinTheta • v := by
    funext j
    apply eisenstein_theta_cancel
    have hj := congrFun (congrArg Subtype.val hw) j
    change eisensteinTheta*w.val j = eisensteinHeavyUnitCoordinates i j-eisensteinHeavyUnitCoordinates k j at hj
    change eisensteinTheta*w.val j = eisensteinTheta*(eisensteinTheta*v j)
    dsimp [eisensteinHeavyUnitCoordinates,v] at *
    linear_combination hj + ((Pi.single i (1 : Eisenstein) : EisensteinCoordinates) j-
      (Pi.single k (1 : Eisenstein) : EisensteinCoordinates) j)*eisensteinTheta_sq
  have hc : eisensteinWordResidue v ∈ ternaryGolay :=
    eisensteinLeechModule_theta_code v (he ▸ w.property)
  have hv (j : Fin 12) : eisensteinWordResidue v j =
      -(if j=i then 1 else 0)+(if j=k then 1 else 0) := by
    simp [v,eisensteinWordResidue,Pi.single_apply]
  have hwle : ternaryWeight (eisensteinWordResidue v) ≤ 2 := by
    have hs : (Finset.univ.filter (fun j => eisensteinWordResidue v j≠0)) ⊆ {i,k} := by
      intro j hj
      simp only [Finset.mem_insert,Finset.mem_singleton]
      by_contra hh
      have hjn := (Finset.mem_filter.mp hj).2
      simp only [not_or] at hh
      exact hjn (by rw [hv]; simp [hh.1,hh.2])
    exact (Finset.card_le_card hs).trans (by have h := Finset.card_pair_eq_one_or_two (a := i) (b := k); omega)
  have hz : eisensteinWordResidue v=0 := by
    by_contra hn
    have hm := ternaryGolay_minimum _ hc hn
    omega
  by_contra hik
  have hh := congrFun hz i
  rw [hv] at hh
  simp [hik] at hh

theorem eisensteinHeavyUnitFrame_eq_iff (i k : Fin 12) (t s : ternaryGolay) :
    eisensteinHeavyUnitFrame i t = eisensteinHeavyUnitFrame k s ↔
      i=k ∧ t-s ∈ ternaryConstants := by
  constructor
  · intro h
    have hc := eisensteinHeavyUnitFrame_constants i k t s h
    refine ⟨?_,hc⟩
    have hh := (eisensteinFramePair_eq_iff _ _).mp (congrArg Subtype.val h)
    have he : eisensteinClass (eisensteinHeavyPhaseVector i t).val =
        eisensteinClass (eisensteinHeavyPhaseVector k s).val :=
      hh.resolve_right (eisensteinHeavyPhase_class_not_neg i k t s)
    rw [eisensteinHeavyPhase_class_of_constants i t s hc] at he
    have hs := congrArg (eisensteinClassAction (eisensteinPhaseIsometries (Multiplicative.ofAdd (-s)))) he
    rw [eisensteinClassAction_mk,eisensteinClassAction_mk,
      eisensteinHeavyPhase_strip,eisensteinHeavyPhase_strip] at hs
    exact eisensteinHeavyUnit_class_injective hs
  · rintro ⟨rfl,hc⟩
    apply Subtype.ext
    exact congrArg eisensteinFramePair (eisensteinHeavyPhase_class_of_constants _ t s hc)


/-- The structural family consisting of frames carrying a (16,1^11) vector
obtained by actual code phases and a marked coordinate. -/
def eisensteinHeavyUnitFrames : Set EisensteinFrame :=
  Set.range (fun p : Fin 12 × ternaryGolay => eisensteinHeavyUnitFrame p.1 p.2)

def eisensteinHeavyPhaseRepresentative (v : TernaryPhaseModule) : ternaryGolay :=
  (ternaryConstants.mkQ_surjective v).choose

theorem eisensteinHeavyPhaseRepresentative_mk (v : TernaryPhaseModule) :
    ternaryConstants.mkQ (eisensteinHeavyPhaseRepresentative v) = v :=
  (ternaryConstants.mkQ_surjective v).choose_spec

def eisensteinHeavyUnitFrameParameter (p : Fin 12 × TernaryPhaseModule) : eisensteinHeavyUnitFrames :=
  ⟨eisensteinHeavyUnitFrame p.1 (eisensteinHeavyPhaseRepresentative p.2),⟨(p.1,eisensteinHeavyPhaseRepresentative p.2),rfl⟩⟩

theorem eisensteinHeavyUnitFrameParameter_injective :
    Function.Injective eisensteinHeavyUnitFrameParameter := by
  intro p q h
  have hh := (eisensteinHeavyUnitFrame_eq_iff _ _ _ _).mp (congrArg Subtype.val h)
  refine Prod.ext hh.1 ?_
  have he := (Submodule.Quotient.eq ternaryConstants).mpr hh.2
  change ternaryConstants.mkQ (eisensteinHeavyPhaseRepresentative p.2) =
    ternaryConstants.mkQ (eisensteinHeavyPhaseRepresentative q.2) at he
  simpa only [eisensteinHeavyPhaseRepresentative_mk] using he

theorem eisensteinHeavyUnitFrameParameter_surjective :
    Function.Surjective eisensteinHeavyUnitFrameParameter := by
  rintro ⟨F,⟨⟨i,t⟩,rfl⟩⟩
  refine ⟨(i,ternaryConstants.mkQ t),?_⟩
  apply Subtype.ext
  apply (eisensteinHeavyUnitFrame_eq_iff _ _ _ _).mpr
  refine ⟨rfl,?_⟩
  exact (Submodule.Quotient.eq ternaryConstants).mp
    (eisensteinHeavyPhaseRepresentative_mk (ternaryConstants.mkQ t))

/-- Coordinate marking and the actual five-dimensional phase module classify
this family, with no enumeration of frames. -/
def eisensteinHeavyUnitFramesEquiv :
    (Fin 12 × TernaryPhaseModule) ≃ eisensteinHeavyUnitFrames :=
  Equiv.ofBijective eisensteinHeavyUnitFrameParameter
    ⟨eisensteinHeavyUnitFrameParameter_injective,eisensteinHeavyUnitFrameParameter_surjective⟩

theorem eisensteinHeavyUnitFrames_card : Nat.card eisensteinHeavyUnitFrames = 2916 := by
  rw [← Nat.card_congr eisensteinHeavyUnitFramesEquiv,Nat.card_prod,ternaryPhaseModule_card]
  norm_num [Nat.card_eq_fintype_card]

end Atlas.Conway
