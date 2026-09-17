import Atlas.Conway.EisensteinPairUnitParameters

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def eisensteinOrderedPairMap (g : TernaryPureAutomorphism) (p : EisensteinOrderedPair) : EisensteinOrderedPair :=
  ⟨(g.val p.val.1,g.val p.val.2),fun h => p.property (g.val.injective h)⟩

theorem eisensteinCodePhaseFrame_action (a t : ternaryGolay) (x : EisensteinShell 6) :
    eisensteinPhaseIsometries (Multiplicative.ofAdd a) • eisensteinFrameOfVector (eisensteinCodePhaseShell t x) =
      eisensteinFrameOfVector (eisensteinCodePhaseShell (a+t) x) := by
  rw [eisensteinFrameAction_vector]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext j
  change (eisensteinIntegralAction (eisensteinPhaseIsometries (Multiplicative.ofAdd a))
    (eisensteinCodePhaseShell t x).val).val j = _
  rw [eisensteinIntegralAction_phase_apply,eisensteinCodePhaseShell_apply,eisensteinCodePhaseShell_apply]
  change eisensteinPhase (a.val j)*(eisensteinPhase (t.val j)*_) = eisensteinPhase (a.val j+t.val j)*_
  rw [eisensteinPhase_add,mul_assoc]

theorem eisensteinPairUnitFrame_coordinate (g : TernaryPureAutomorphism) (b : Bool)
    (p : EisensteinOrderedPair) (t : ternaryGolay) :
    eisensteinCoordinateIsometries g • eisensteinPairUnitFrame b p t =
      eisensteinPairUnitFrame b (eisensteinOrderedPairMap g p) (ternaryPureCodeEnd g t) := by
  rw [eisensteinPairUnitFrame,eisensteinFrameAction_vector]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext j
  change (eisensteinIntegralAction (eisensteinCoordinateIsometries g)
    (eisensteinCodePhaseShell t (eisensteinPairUnitVector b p)).val).val j = _
  rw [eisensteinIntegralAction_coordinate_apply,eisensteinCodePhaseShell_apply,eisensteinCodePhaseShell_apply]
  change eisensteinPhase (t.val (g.val.symm j))*eisensteinPairUnitCoordinates b p (g.val.symm j) =
    eisensteinPhase (t.val (g.val.symm j))*eisensteinPairUnitCoordinates b (eisensteinOrderedPairMap g p) j
  congr 1
  have he (i : Fin 12) : g.val.symm j=i ↔ j=g.val i := by
    constructor
    · intro h; exact (g.val.apply_symm_apply j).symm.trans (congrArg g.val h)
    · intro h; rw [h,g.val.symm_apply_apply]
  simp [eisensteinPairUnitCoordinates,eisensteinPairUnitA,eisensteinOrderedPairMap,Pi.smul_apply,Pi.single_apply,he]

theorem eisensteinPairUnitFrame_parameter_action (q : EisensteinMonomialParameters)
    (b : Bool) (p : EisensteinOrderedPair) (t : ternaryGolay) :
    eisensteinMonomialParameterIsometry q • eisensteinPairUnitFrame b p t =
      eisensteinPairUnitFrame b (eisensteinOrderedPairMap q.2.2 p) (q.2.1+ternaryPureCodeEnd q.2.2 t) := by
  unfold eisensteinMonomialParameterIsometry
  rw [mul_smul,mul_smul,eisensteinPairUnitFrame_coordinate]
  change (if q.1 then eisensteinSignIsometry else 1) •
    (eisensteinPhaseIsometries (Multiplicative.ofAdd q.2.1) • eisensteinFrameOfVector _) = _
  rw [eisensteinCodePhaseFrame_action]
  cases q.1 <;> simp [eisensteinSignIsometry_frame,eisensteinPairUnitFrame]

theorem eisensteinPairUnitFrames_preserved (g : eisensteinCoordinateFrameStabilizer)
    (b : Bool) (F : EisensteinFrame) (hF : F ∈ eisensteinPairUnitFrames b) :
    g • F ∈ eisensteinPairUnitFrames b := by
  obtain ⟨⟨p,t⟩,rfl⟩ := hF
  obtain ⟨q,rfl⟩ := eisensteinFrameFromParameters_surjective g
  change eisensteinMonomialParameterIsometry q • eisensteinPairUnitFrame b p t ∈ _
  rw [eisensteinPairUnitFrame_parameter_action]
  exact ⟨(eisensteinOrderedPairMap q.2.2 p,q.2.1+ternaryPureCodeEnd q.2.2 t),rfl⟩

def eisensteinOrderedBasePair : EisensteinOrderedPair := ⟨(0,1),by decide⟩

theorem eisensteinPairUnitFrame_reachable (b : Bool) (p : EisensteinOrderedPair) (t : ternaryGolay) :
    ∃ g : eisensteinCoordinateFrameStabilizer,
      g • eisensteinPairUnitFrame b eisensteinOrderedBasePair 0=eisensteinPairUnitFrame b p t := by
  letI := ternaryPureAutomorphism_three_transitive
  have h2 : MulAction.IsMultiplyPretransitive TernaryPureAutomorphism (Fin 12) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := 3) (by decide) (by norm_num)
  obtain ⟨g,hg0,hg1⟩ := MulAction.is_two_pretransitive_iff.mp h2 (by decide : (0 : Fin 12)≠1) p.property
  have hp : eisensteinOrderedPairMap g eisensteinOrderedBasePair=p := by
    apply Subtype.ext
    exact Prod.ext hg0 hg1
  refine ⟨eisensteinFrameFromParameters (false,t,g),?_⟩
  change eisensteinMonomialParameterIsometry (false,t,g) • eisensteinPairUnitFrame b eisensteinOrderedBasePair 0 = _
  rw [eisensteinPairUnitFrame_parameter_action,hp,map_zero,add_zero]

theorem eisensteinPairUnitFrames_orbit (b : Bool) :
    eisensteinPairUnitFrames b = MulAction.orbit eisensteinCoordinateFrameStabilizer
      (eisensteinPairUnitFrame b eisensteinOrderedBasePair 0) := by
  ext F
  constructor
  · rintro ⟨⟨p,t⟩,rfl⟩
    exact MulAction.mem_orbit_iff.mpr (eisensteinPairUnitFrame_reachable b p t)
  · intro hF
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hF
    exact eisensteinPairUnitFrames_preserved g b _ ⟨(eisensteinOrderedBasePair,0),rfl⟩

theorem eisensteinPairUnitOrbit_card (b : Bool) :
    Nat.card (MulAction.orbit eisensteinCoordinateFrameStabilizer
      (eisensteinPairUnitFrame b eisensteinOrderedBasePair 0))=16038 := by
  rw [← eisensteinPairUnitFrames_orbit]
  exact eisensteinPairUnitFrames_card b

end Atlas.Conway
