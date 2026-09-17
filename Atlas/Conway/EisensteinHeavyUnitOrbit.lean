import Atlas.Conway.EisensteinHeavyUnitFrames
import Atlas.Conway.EisensteinProjectiveAction

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem eisensteinHeavyUnitFrame_phase (a t : ternaryGolay) (i : Fin 12) :
    eisensteinPhaseIsometries (Multiplicative.ofAdd a) • eisensteinHeavyUnitFrame i t =
      eisensteinHeavyUnitFrame i (a+t) := by
  rw [eisensteinHeavyUnitFrame,eisensteinFrameAction_vector]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext j
  change (eisensteinIntegralAction (eisensteinPhaseIsometries (Multiplicative.ofAdd a))
    (eisensteinHeavyPhaseVector i t).val).val j = (eisensteinHeavyPhaseVector i (a+t)).val.val j
  rw [eisensteinIntegralAction_phase_apply,eisensteinHeavyPhaseVector_apply,
    eisensteinHeavyPhaseVector_apply]
  change eisensteinPhase (a.val j)*(eisensteinPhase (t.val j)*_) =
    eisensteinPhase (a.val j+t.val j)*_
  rw [eisensteinPhase_add,mul_assoc]

theorem eisensteinIntegralAction_coordinate_apply (g : TernaryPureAutomorphism)
    (x : EisensteinLattice) (j : Fin 12) :
    (eisensteinIntegralAction (eisensteinCoordinateIsometries g) x).val j = x.val (g.val.symm j) := by
  apply eisensteinToRational_injective
  exact congrFun (eisensteinIntegralAction_agrees (eisensteinCoordinateIsometries g) x) j

theorem eisensteinHeavyUnitFrame_coordinate (g : TernaryPureAutomorphism) (t : ternaryGolay)
    (i : Fin 12) :
    eisensteinCoordinateIsometries g • eisensteinHeavyUnitFrame i t =
      eisensteinHeavyUnitFrame (g.val i) (ternaryPureCodeEnd g t) := by
  rw [eisensteinHeavyUnitFrame,eisensteinFrameAction_vector]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext j
  change (eisensteinIntegralAction (eisensteinCoordinateIsometries g)
    (eisensteinHeavyPhaseVector i t).val).val j = _
  rw [eisensteinIntegralAction_coordinate_apply,eisensteinHeavyPhaseVector_apply,
    eisensteinHeavyPhaseVector_apply]
  change eisensteinPhase (t.val (g.val.symm j))*eisensteinHeavyUnitCoordinates i (g.val.symm j) =
    eisensteinPhase (t.val (g.val.symm j))*eisensteinHeavyUnitCoordinates (g.val i) j
  congr 1
  have he : g.val.symm j=i ↔ j=g.val i := by
    constructor
    · intro h; exact (g.val.apply_symm_apply j).symm.trans (congrArg g.val h)
    · intro h; rw [h,g.val.symm_apply_apply]
  simp [eisensteinHeavyUnitCoordinates,Pi.single_apply,he]

theorem eisensteinSignIsometry_frame (F : EisensteinFrame) : eisensteinSignIsometry • F = F := by
  obtain ⟨c,hc,he⟩ := eisensteinFrame_pair F
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hc
  have hF : F=eisensteinFrameOfVector x := Subtype.ext he
  rw [hF,eisensteinFrameAction_vector]
  apply Subtype.ext
  have hx : eisensteinIntegralAction eisensteinSignIsometry x.val = -x.val := by
    apply Subtype.ext
    apply eisensteinCoordinateEmbedding_injective
    rw [eisensteinIntegralAction_agrees]
    exact (map_neg eisensteinCoordinateEmbedding x.val.val).symm
  change eisensteinFramePair (eisensteinClass (eisensteinIntegralAction eisensteinSignIsometry x.val)) = _
  rw [hx,map_neg,eisensteinFramePair_neg]
  rfl

theorem eisensteinHeavyUnitFrame_parameter_action (p : EisensteinMonomialParameters)
    (i : Fin 12) (t : ternaryGolay) :
    eisensteinMonomialParameterIsometry p • eisensteinHeavyUnitFrame i t =
      eisensteinHeavyUnitFrame (p.2.2.val i) (p.2.1+ternaryPureCodeEnd p.2.2 t) := by
  unfold eisensteinMonomialParameterIsometry
  rw [mul_smul,mul_smul,eisensteinHeavyUnitFrame_coordinate,eisensteinHeavyUnitFrame_phase]
  cases p.1 <;> simp [eisensteinSignIsometry_frame]

theorem eisensteinHeavyUnitFrames_preserved (g : eisensteinCoordinateFrameStabilizer)
    (F : EisensteinFrame) (hF : F ∈ eisensteinHeavyUnitFrames) : g • F ∈ eisensteinHeavyUnitFrames := by
  obtain ⟨⟨i,t⟩,rfl⟩ := hF
  obtain ⟨p,rfl⟩ := eisensteinFrameFromParameters_surjective g
  change eisensteinMonomialParameterIsometry p • eisensteinHeavyUnitFrame i t ∈ _
  rw [eisensteinHeavyUnitFrame_parameter_action]
  exact ⟨(p.2.2.val i,p.2.1+ternaryPureCodeEnd p.2.2 t),rfl⟩


theorem eisensteinHeavyUnitFrame_reachable (i : Fin 12) (t : ternaryGolay) :
    ∃ g : eisensteinCoordinateFrameStabilizer,
      g • eisensteinHeavyUnitFrame 0 0 = eisensteinHeavyUnitFrame i t := by
  letI := ternaryPureAutomorphism_three_transitive
  letI : MulAction.IsMultiplyPretransitive TernaryPureAutomorphism (Fin 12) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := 3) (by decide) (by norm_num)
  letI : MulAction.IsPretransitive TernaryPureAutomorphism (Fin 12) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq TernaryPureAutomorphism (0 : Fin 12) i
  change g.val 0=i at hg
  refine ⟨eisensteinFrameFromParameters (false,t,g),?_⟩
  change eisensteinMonomialParameterIsometry (false,t,g) • eisensteinHeavyUnitFrame 0 0 = _
  rw [eisensteinHeavyUnitFrame_parameter_action,hg,map_zero,add_zero]

/-- The 2916 structurally parameterized frames are one full coordinate-stabilizer orbit. -/
theorem eisensteinHeavyUnitFrames_orbit :
    eisensteinHeavyUnitFrames = MulAction.orbit eisensteinCoordinateFrameStabilizer
      (eisensteinHeavyUnitFrame 0 0) := by
  ext F
  constructor
  · rintro ⟨⟨i,t⟩,rfl⟩
    exact MulAction.mem_orbit_iff.mpr (eisensteinHeavyUnitFrame_reachable i t)
  · intro hF
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hF
    exact eisensteinHeavyUnitFrames_preserved g _ ⟨(0,0),rfl⟩

theorem eisensteinHeavyUnitOrbit_card :
    Nat.card (MulAction.orbit eisensteinCoordinateFrameStabilizer (eisensteinHeavyUnitFrame 0 0)) = 2916 := by
  rw [← eisensteinHeavyUnitFrames_orbit]
  exact eisensteinHeavyUnitFrames_card

theorem eisensteinHeavyUnitFrames_transitive (F G : EisensteinFrame)
    (hF : F ∈ eisensteinHeavyUnitFrames) (hG : G ∈ eisensteinHeavyUnitFrames) :
    ∃ g : eisensteinCoordinateFrameStabilizer, g • F = G := by
  rw [eisensteinHeavyUnitFrames_orbit] at hF hG
  obtain ⟨f,hf⟩ := MulAction.mem_orbit_iff.mp hF
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hG
  refine ⟨g*f⁻¹,?_⟩
  rw [mul_smul,← hf,inv_smul_smul,hg]

end Atlas.Conway
