import Atlas.Conway.EisensteinHexadTransitive

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped Pointwise
attribute [local instance] Classical.propDecidable

private theorem hexadFamily_mem (F : EisensteinFrame) :
    F ∈ eisensteinHexadFamily ↔ ∃ p : TernaryConstantHexadPair, F ∈ eisensteinHexadPairOrbit p := by
  change F ∈ Finset.univ.biUnion eisensteinHexadPairOrbit ↔ _
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]

def eisensteinHexadPermutedPhase (g : TernaryPureAutomorphism)
    (t : Multiplicative ternaryGolay) : Multiplicative ternaryGolay := Multiplicative.ofAdd
  ⟨fun i => t.toAdd.val (g.val.symm i),g.property _ t.toAdd.property⟩

theorem eisensteinHexadCoordinatePhase_mul (g : TernaryPureAutomorphism)
    (t : Multiplicative ternaryGolay) :
    eisensteinCoordinateIsometries g * eisensteinPhaseIsometries t =
      eisensteinPhaseIsometries (eisensteinHexadPermutedPhase g t) * eisensteinCoordinateIsometries g := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  funext i
  rfl

theorem eisensteinHexadFamily_coordinate (g : TernaryPureAutomorphism) (F : EisensteinFrame)
    (hF : F ∈ eisensteinHexadFamily) : eisensteinCoordinateIsometries g • F ∈ eisensteinHexadFamily := by
  obtain ⟨p,hp⟩ := (hexadFamily_mem F).mp hF
  obtain ⟨t,ht⟩ := (eisensteinHexadPairOrbit_mem p F).mp hp
  let tp := eisensteinHexadPermutedPhase g t
  have he : eisensteinCoordinateIsometries g • F =
      eisensteinPhaseIsometries tp • eisensteinHexadPairFrame (g • p) := by
    calc
      _ = eisensteinCoordinateIsometries g •
          (eisensteinPhaseIsometries t • eisensteinHexadPairFrame p) :=
        congrArg (fun X : EisensteinFrame => eisensteinCoordinateIsometries g • X) ht.symm
      _ = (eisensteinCoordinateIsometries g * eisensteinPhaseIsometries t) •
          eisensteinHexadPairFrame p := (mul_smul _ _ _).symm
      _ = (eisensteinPhaseIsometries tp * eisensteinCoordinateIsometries g) •
          eisensteinHexadPairFrame p := congrArg (fun h : eisensteinHermitianGroup =>
            h • eisensteinHexadPairFrame p) (eisensteinHexadCoordinatePhase_mul g t)
      _ = eisensteinPhaseIsometries tp •
          (eisensteinCoordinateIsometries g • eisensteinHexadPairFrame p) := mul_smul _ _ _
      _ = _ := congrArg (fun X : EisensteinFrame => eisensteinPhaseIsometries tp • X)
        (eisensteinHexadPairFrame_coordinate p (g • p) g rfl)
  exact (hexadFamily_mem _).mpr ⟨g • p,(eisensteinHexadPairOrbit_mem _ _).mpr ⟨tp,he.symm⟩⟩

private theorem hexad_sign_frame (F : EisensteinFrame) : eisensteinSignIsometry • F=F := by
  have he : eisensteinSignIsometry=eisensteinUnitIsometries (-1) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    rw [eisensteinUnitIsometries_apply]
    change -z=eisensteinToRational (-1) • z
    simp
  rw [he,eisensteinUnitIsometries_frame]

/-- The parametrized family is invariant under the full, already identified local subgroup. -/
theorem eisensteinHexadFamily_preserved (g : eisensteinCoordinateFrameStabilizer)
    (F : EisensteinFrame) (hF : F ∈ eisensteinHexadFamily) : g.val • F ∈ eisensteinHexadFamily := by
  obtain ⟨p,rfl⟩ := eisensteinFrameFromParameters_surjective g
  change eisensteinMonomialParameterIsometry p • F ∈ eisensteinHexadFamily
  rw [eisensteinMonomialParameterIsometry,mul_smul,mul_smul]
  have h := eisensteinHexadFamily_phase (Multiplicative.ofAdd p.2.1) _
    (eisensteinHexadFamily_coordinate p.2.2 F hF)
  cases hp : p.1 <;> simpa [hp,hexad_sign_frame] using h

/-- This is a full local-subgroup orbit, rather than merely a transitive subset. -/
theorem eisensteinHexadFamily_orbit (F : EisensteinFrame) (hF : F ∈ eisensteinHexadFamily) :
    MulAction.orbit eisensteinCoordinateFrameStabilizer F = {G | G ∈ eisensteinHexadFamily} := by
  ext G
  constructor
  · rintro ⟨g,rfl⟩
    exact eisensteinHexadFamily_preserved g F hF
  · intro hG
    obtain ⟨g,hg⟩ := eisensteinHexadFamily_transitive F G hF hG
    exact ⟨g,hg⟩

end Atlas.Conway
