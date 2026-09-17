import Atlas.Conway.EisensteinTriadUnitParameters

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def eisensteinTriadEmbeddingMap (g : TernaryPureAutomorphism) (e : Fin 3 ↪ Fin 12) : Fin 3 ↪ Fin 12 :=
  e.trans g.val.toEmbedding

theorem eisensteinTriadUnitFrame_coordinate (g : TernaryPureAutomorphism) (r : Fin 3)
    (e : Fin 3 ↪ Fin 12) (t : ternaryGolay) :
    eisensteinCoordinateIsometries g • eisensteinTriadUnitFrame r e t =
      eisensteinTriadUnitFrame r (eisensteinTriadEmbeddingMap g e) (ternaryPureCodeEnd g t) := by
  rw [eisensteinTriadUnitFrame,eisensteinFrameAction_vector]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext j
  change (eisensteinIntegralAction (eisensteinCoordinateIsometries g)
    (eisensteinCodePhaseShell t (eisensteinTriadUnitVector r e)).val).val j = _
  rw [eisensteinIntegralAction_coordinate_apply,eisensteinCodePhaseShell_apply,eisensteinCodePhaseShell_apply]
  change eisensteinPhase (t.val (g.val.symm j))*eisensteinTriadUnitCoordinates r e (g.val.symm j) =
    eisensteinPhase (t.val (g.val.symm j))*eisensteinTriadUnitCoordinates r (eisensteinTriadEmbeddingMap g e) j
  congr 1
  have he (i : Fin 12) : g.val.symm j=i ↔ j=g.val i := by
    constructor
    · intro h; exact (g.val.apply_symm_apply j).symm.trans (congrArg g.val h)
    · intro h; rw [h,g.val.symm_apply_apply]
  simp [eisensteinTriadUnitCoordinates,eisensteinTriadUnitA,eisensteinTriadEmbeddingMap,
    Pi.smul_apply,Pi.single_apply,he]

theorem eisensteinTriadUnitFrame_parameter_action (q : EisensteinMonomialParameters)
    (r : Fin 3) (e : Fin 3 ↪ Fin 12) (t : ternaryGolay) :
    eisensteinMonomialParameterIsometry q • eisensteinTriadUnitFrame r e t =
      eisensteinTriadUnitFrame r (eisensteinTriadEmbeddingMap q.2.2 e) (q.2.1+ternaryPureCodeEnd q.2.2 t) := by
  unfold eisensteinMonomialParameterIsometry
  rw [mul_smul,mul_smul,eisensteinTriadUnitFrame_coordinate]
  change (if q.1 then eisensteinSignIsometry else 1) •
    (eisensteinPhaseIsometries (Multiplicative.ofAdd q.2.1) • eisensteinFrameOfVector _) = _
  rw [eisensteinCodePhaseFrame_action]
  cases q.1 <;> simp [eisensteinSignIsometry_frame,eisensteinTriadUnitFrame]

theorem eisensteinTriadUnitFrames_preserved (g : eisensteinCoordinateFrameStabilizer)
    (r : Fin 3) (F : EisensteinFrame) (hF : F ∈ eisensteinTriadUnitFrames r) :
    g • F ∈ eisensteinTriadUnitFrames r := by
  obtain ⟨⟨e,t⟩,rfl⟩ := hF
  obtain ⟨q,rfl⟩ := eisensteinFrameFromParameters_surjective g
  change eisensteinMonomialParameterIsometry q • eisensteinTriadUnitFrame r e t ∈ _
  rw [eisensteinTriadUnitFrame_parameter_action]
  exact ⟨(eisensteinTriadEmbeddingMap q.2.2 e,q.2.1+ternaryPureCodeEnd q.2.2 t),rfl⟩

def eisensteinBaseTriadEmbedding : Fin 3 ↪ Fin 12 := Fin.castLEEmb (by decide)

theorem eisensteinTriadUnitFrame_reachable (r : Fin 3) (e : Fin 3 ↪ Fin 12) (t : ternaryGolay) :
    ∃ g : eisensteinCoordinateFrameStabilizer,
      g • eisensteinTriadUnitFrame r eisensteinBaseTriadEmbedding 0=eisensteinTriadUnitFrame r e t := by
  letI := ternaryPureAutomorphism_three_transitive
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq TernaryPureAutomorphism eisensteinBaseTriadEmbedding e
  have he : eisensteinTriadEmbeddingMap g eisensteinBaseTriadEmbedding=e := hg
  refine ⟨eisensteinFrameFromParameters (false,t,g),?_⟩
  change eisensteinMonomialParameterIsometry (false,t,g) •
    eisensteinTriadUnitFrame r eisensteinBaseTriadEmbedding 0 = _
  rw [eisensteinTriadUnitFrame_parameter_action,he,map_zero,add_zero]

theorem eisensteinTriadUnitFrames_orbit (r : Fin 3) :
    eisensteinTriadUnitFrames r = MulAction.orbit eisensteinCoordinateFrameStabilizer
      (eisensteinTriadUnitFrame r eisensteinBaseTriadEmbedding 0) := by
  ext F
  constructor
  · rintro ⟨⟨e,t⟩,rfl⟩
    exact MulAction.mem_orbit_iff.mpr (eisensteinTriadUnitFrame_reachable r e t)
  · intro hF
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hF
    exact eisensteinTriadUnitFrames_preserved g r _ ⟨(eisensteinBaseTriadEmbedding,0),rfl⟩

theorem eisensteinTriadUnitOrbit_card (r : Fin 3) :
    Nat.card (MulAction.orbit eisensteinCoordinateFrameStabilizer
      (eisensteinTriadUnitFrame r eisensteinBaseTriadEmbedding 0))=40095 := by
  rw [← eisensteinTriadUnitFrames_orbit]
  exact eisensteinTriadUnitFrames_card r

end Atlas.Conway
