import Atlas.Conway.EisensteinHexadFamily
import Atlas.Conway.EisensteinFrameOrder
import Atlas.Conway.EisensteinFrameGroup
import Atlas.Conway.EisensteinProjectiveAction

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped Pointwise
attribute [local instance] Classical.propDecidable

private theorem hexadFrame_eq_of_pair (s r : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (hr : r ∈ ternaryConstantHexads)
    (i j : Fin 12) (hi : i ∈ s) (hj : j ∈ r)
    (h : ternaryConstantHexadPair s=ternaryConstantHexadPair r) :
    eisensteinHexadFrame s hs i hi=eisensteinHexadFrame r hr j hj := by
  rcases (ternaryConstantHexadPair_eq_iff s r).mp h with h|h
  · subst r; exact eisensteinHexadFrame_independent s hs i j hi hj
  · subst s
    exact (eisensteinHexadFrame_compl r hr j i hj hi).symm

theorem eisensteinHexadFrame_coordinate (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) (hi : i ∈ s)
    (g : TernaryPureAutomorphism) :
    eisensteinCoordinateIsometries g • eisensteinHexadFrame s hs i hi =
      eisensteinHexadFrame (s.map g.val.toEmbedding) (ternaryConstantHexads_permute g s hs)
        (g.val i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩) := by
  rw [eisensteinHexadFrame,eisensteinFrameAction_vector]
  apply congrArg eisensteinFrameOfVector
  apply Subtype.ext
  apply Subtype.ext
  apply eisensteinCoordinateEmbedding_injective
  change eisensteinCoordinateEmbedding
    (eisensteinIntegralAction (eisensteinCoordinateIsometries g)
      (eisensteinHexadLatticeVector s hs i)).val = _
  rw [eisensteinIntegralAction_agrees]
  funext j
  change eisensteinToRational (eisensteinHexadVector s i (g.val.symm j)) =
    eisensteinToRational (eisensteinHexadVector (s.map g.val.toEmbedding) (g.val i) j)
  congr 1
  simp [eisensteinHexadVector,eisensteinHexadLift,Pi.smul_apply,
    Finset.mem_map_equiv,Equiv.symm_apply_eq]

theorem eisensteinHexadPairFrame_coordinate (p q : TernaryConstantHexadPair)
    (g : TernaryPureAutomorphism) (hg : g • p=q) :
    eisensteinCoordinateIsometries g • eisensteinHexadPairFrame p=eisensteinHexadPairFrame q := by
  rw [eisensteinHexadPairFrame,eisensteinHexadFrame_coordinate]
  apply hexadFrame_eq_of_pair
  have he := congrArg Subtype.val hg
  change g • p.val=q.val at he
  rw [← eisensteinHexadPairSupport_pair p,← eisensteinHexadPairSupport_pair q,
    ternaryConstantHexadPair_smul,ternaryFinset_smul] at he
  exact he

/-- The full standard-frame stabilizer is transitive on the intrinsic family of891 frames. -/
theorem eisensteinHexadFamily_transitive (F G : EisensteinFrame)
    (hF : F ∈ eisensteinHexadFamily) (hG : G ∈ eisensteinHexadFamily) :
    ∃ g : eisensteinCoordinateFrameStabilizer, g.val • F=G := by
  obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hF
  obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hG
  obtain ⟨t,ht⟩ := (eisensteinHexadPairOrbit_mem p F).mp hp
  obtain ⟨u,hu⟩ := (eisensteinHexadPairOrbit_mem q G).mp hq
  obtain ⟨g,hg⟩ := ternaryConstantHexadPairs_transitive p q
  let pt := eisensteinFrameFromParameters (false,t.toAdd,1)
  let pu := eisensteinFrameFromParameters (false,u.toAdd,1)
  let pg := eisensteinFrameFromParameters (false,0,g)
  have hpt : pt.val=eisensteinPhaseIsometries t := by
    simp [pt,eisensteinFrameFromParameters,eisensteinMonomialParameterIsometry]
  have hpu : pu.val=eisensteinPhaseIsometries u := by
    simp [pu,eisensteinFrameFromParameters,eisensteinMonomialParameterIsometry]
  have hpg : pg.val=eisensteinCoordinateIsometries g := by
    simp [pg,eisensteinFrameFromParameters,eisensteinMonomialParameterIsometry]
  refine ⟨pu*pg*pt⁻¹,?_⟩
  change (pu.val*pg.val*pt.val⁻¹) • F=G
  rw [hpt,hpu,hpg,← ht,mul_smul,mul_smul,inv_smul_smul,
    eisensteinHexadPairFrame_coordinate p q g hg,hu]


theorem eisensteinHexadFamily_phase (t : Multiplicative ternaryGolay) (F : EisensteinFrame)
    (hF : F ∈ eisensteinHexadFamily) : eisensteinPhaseIsometries t • F ∈ eisensteinHexadFamily := by
  obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hF
  obtain ⟨u,hu⟩ := (eisensteinHexadPairOrbit_mem p F).mp hp
  apply Finset.mem_biUnion.mpr
  refine ⟨p,Finset.mem_univ _,(eisensteinHexadPairOrbit_mem _ _).mpr ⟨t*u,?_⟩⟩
  rw [map_mul,mul_smul,hu]


end Atlas.Conway
