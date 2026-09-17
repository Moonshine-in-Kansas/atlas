import Atlas.Conway.EisensteinNineHexadInvariant
import Atlas.Codes.TernaryConstantHexadTransitivity

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local irreducible] eisensteinNineHexadFamily
open scoped Pointwise

 theorem eisensteinNineHexadFrame_coordinate (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k j : Fin 12) (hk : k ∈ s) (hj : j ∉ s)
    (b : ZMod 3) (hb : b≠0) (g : TernaryPureAutomorphism) :
    eisensteinCoordinateIsometries g • eisensteinNineHexadFrame s hs k j hk hj b hb=
      eisensteinNineHexadFrame (s.map g.val.toEmbedding) (ternaryConstantHexads_permute g s hs)
        (g.val k) (g.val j) (Finset.mem_map.mpr ⟨k,hk,rfl⟩)
        (by simpa [Finset.mem_map_equiv] using hj) b hb := by
  rw [eisensteinNineHexadFrame,eisensteinFrameAction_vector]
  apply congrArg eisensteinFrameOfVector
  apply Subtype.ext
  apply Subtype.ext
  funext i
  change (eisensteinIntegralAction (eisensteinCoordinateIsometries g)
    (eisensteinNineHexadLatticeVector s hs k j b)).val i=
    eisensteinNineHexadVector (s.map g.val.toEmbedding) (g.val k) (g.val j) b i
  rw [eisensteinIntegralAction_coordinate_apply]
  simp [eisensteinNineHexadShellVector,eisensteinNineHexadLatticeVector,eisensteinNineHexadVector,
    eisensteinNineHexadLift,Pi.smul_apply,Finset.mem_map_equiv,Equiv.symm_apply_eq]

 theorem eisensteinNineHexadPairFrame_mem (b : ZMod 3) (hb : b≠0) (p : TernaryConstantHexadPair) :
    eisensteinNineHexadPairFrame b hb p ∈ eisensteinNineHexadFamily b hb := by
  classical
  rw [eisensteinNineHexadFamily]
  apply Finset.mem_biUnion.mpr
  exact ⟨p,Finset.mem_univ _,(eisensteinNineHexadPairOrbit_mem b hb p _).mpr ⟨1,by simp⟩⟩

/-- Coordinate transport takes the canonical base into the canonical phase orbit
of the transported complementary partition. -/
theorem eisensteinNineHexadPairFrame_coordinate_phase (b : ZMod 3) (hb : b≠0)
    (p : TernaryConstantHexadPair) (g : TernaryPureAutomorphism) :
    ∃ v : Multiplicative ternaryGolay,
      eisensteinPhaseIsometries v • eisensteinNineHexadPairFrame b hb (g • p)=
        eisensteinCoordinateIsometries g • eisensteinNineHexadPairFrame b hb p := by
  classical
  let pg := eisensteinFrameFromParameters (false,0,g)
  have hpg : pg.val=eisensteinCoordinateIsometries g := by
    simp [pg,eisensteinFrameFromParameters,eisensteinMonomialParameterIsometry]
  have hm := eisensteinNineHexadFamily_preserved b hb pg _ (eisensteinNineHexadPairFrame_mem b hb p)
  rw [hpg] at hm
  rw [eisensteinNineHexadFamily] at hm
  obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨v,hv⟩ := (eisensteinNineHexadPairOrbit_mem b hb q _).mp hq
  have hc := eisensteinNineHexadFrame_coordinate _ (eisensteinHexadPairSupport_mem p) _ _
    (eisensteinHexadPairPoint_mem p) (eisensteinNineHexadPairOutside_mem p) b hb g
  change eisensteinCoordinateIsometries g • eisensteinNineHexadPairFrame b hb p=_ at hc
  have hh := hv.trans hc
  have hpq := eisensteinNineHexadFrame_phase_partition _ _
    (ternaryConstantHexads_permute g _ (eisensteinHexadPairSupport_mem p))
    (eisensteinHexadPairSupport_mem q) _ _ _ _
    (Finset.mem_map.mpr ⟨_,eisensteinHexadPairPoint_mem p,rfl⟩)
    (by simpa [Finset.mem_map_equiv] using eisensteinNineHexadPairOutside_mem p)
    (eisensteinHexadPairPoint_mem q) (eisensteinNineHexadPairOutside_mem q) b b hb hb v.toAdd hh
  rw [← ternaryFinset_smul,← ternaryConstantHexadPair_smul,
    eisensteinHexadPairSupport_pair,eisensteinHexadPairSupport_pair] at hpq
  have heq : g • p=q := Subtype.ext hpq
  rw [heq]
  exact ⟨v,hv⟩

/-- Each2673 family is transitive under the actual full coordinate-frame stabilizer. -/
theorem eisensteinNineHexadFamily_transitive (b : ZMod 3) (hb : b≠0)
    (F G : EisensteinFrame) (hF : F ∈ eisensteinNineHexadFamily b hb)
    (hG : G ∈ eisensteinNineHexadFamily b hb) :
    ∃ g : eisensteinCoordinateFrameStabilizer,g.val • F=G := by
  classical
  rw [eisensteinNineHexadFamily] at hF hG
  obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hF
  obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hG
  obtain ⟨t,ht⟩ := (eisensteinNineHexadPairOrbit_mem b hb p F).mp hp
  obtain ⟨u,hu⟩ := (eisensteinNineHexadPairOrbit_mem b hb q G).mp hq
  obtain ⟨g,hg⟩ := ternaryConstantHexadPairs_transitive p q
  obtain ⟨v,hv⟩ := eisensteinNineHexadPairFrame_coordinate_phase b hb p g
  rw [hg] at hv
  let pt := eisensteinFrameFromParameters (false,t.toAdd,1)
  let pu := eisensteinFrameFromParameters (false,u.toAdd,1)
  let pv := eisensteinFrameFromParameters (false,v.toAdd,1)
  let pg := eisensteinFrameFromParameters (false,0,g)
  have hpt : pt.val=eisensteinPhaseIsometries t := by
    simp [pt,eisensteinFrameFromParameters,eisensteinMonomialParameterIsometry]
  have hpu : pu.val=eisensteinPhaseIsometries u := by
    simp [pu,eisensteinFrameFromParameters,eisensteinMonomialParameterIsometry]
  have hpv : pv.val=eisensteinPhaseIsometries v := by
    simp [pv,eisensteinFrameFromParameters,eisensteinMonomialParameterIsometry]
  have hpg : pg.val=eisensteinCoordinateIsometries g := by
    simp [pg,eisensteinFrameFromParameters,eisensteinMonomialParameterIsometry]
  refine ⟨pu*pv⁻¹*pg*pt⁻¹,?_⟩
  change (pu.val*pv.val⁻¹*pg.val*pt.val⁻¹) • F=G
  rw [hpt,hpu,hpv,hpg,← ht]
  simp only [mul_smul]
  rw [inv_smul_smul,← hv,inv_smul_smul,hu]

/-- Exact full local-group orbit equality for each of the two2673-frame families. -/
theorem eisensteinNineHexadFamily_orbit (b : ZMod 3) (hb : b≠0)
    (F : EisensteinFrame) (hF : F ∈ eisensteinNineHexadFamily b hb) :
    MulAction.orbit eisensteinCoordinateFrameStabilizer F={G | G ∈ eisensteinNineHexadFamily b hb} := by
  ext G
  constructor
  · rintro ⟨g,rfl⟩
    exact eisensteinNineHexadFamily_preserved b hb g F hF
  · intro hG
    obtain ⟨g,hg⟩ := eisensteinNineHexadFamily_transitive b hb F G hF hG
    exact ⟨g,hg⟩

end Atlas.Conway
