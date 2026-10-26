import Atlas.Rudvalis.SecondFrameCyclic
import Atlas.Rudvalis.SecondFrameGaussian

namespace Atlas.Rudvalis

def distinguishedSecondMask : Finset SeedCoordinate :=
  Finset.univ.filter (fun z => z.1=0 ∨ z.1=4 ∨ z.1=5)

theorem distinguishedSecondMask_cyclic : distinguishedSecondMask=
    frameGlueMask.map (secondFrameCyclicPerm^4).toEmbedding := by
  ext z
  rw [Finset.mem_map_equiv,frameGlueMask_mem_iff_row]
  simp only [distinguishedSecondMask,Finset.mem_filter,Finset.mem_univ,true_and]
  decide +kernel +revert

noncomputable def distinguishedReflection : RationalSpace ≃ₗ[ℚ] RationalSpace :=
  secondFrameReflection distinguishedSecondMask

theorem distinguishedReflection_cyclic (v : RationalSpace) :
    rationalMonomialHom (codeP^4).val (frameGlueReflection v)=
      distinguishedReflection (rationalMonomialHom (codeP^4).val v) := by
  change rationalMonomialHom (codeP^4).val ((2 : ℚ) • secondFrameProjection frameGlueMask v-v)=
    (2 : ℚ) • secondFrameProjection distinguishedSecondMask (rationalMonomialHom (codeP^4).val v)-
      rationalMonomialHom (codeP^4).val v
  rw [map_sub,map_smul,secondFrameProjection_cyclic,distinguishedSecondMask_cyclic]

theorem distinguishedReflection_pairing (v w : RationalSpace) :
    rationalDot (distinguishedReflection v) (distinguishedReflection w)=rationalDot v w :=
  secondFrameReflection_pairing distinguishedSecondMask v w

theorem distinguishedReflection_involutive : Function.Involutive distinguishedReflection :=
  secondFrameReflection_involutive distinguishedSecondMask

theorem distinguishedReflection_gaussian (v : RationalSpace) :
    distinguishedReflection (rationalI v)=rationalI (distinguishedReflection v) := by
  obtain ⟨w,rfl⟩ := (rationalMonomialHom (codeP^4).val).surjective v
  rw [←codeGroup_rational_gaussian_linear,←distinguishedReflection_cyclic,
    frameGlueReflection_gaussian,codeGroup_rational_gaussian_linear,distinguishedReflection_cyclic]

theorem distinguishedReflection_lattice_of_glue_embedding
    (hEmbedding : ∀w : RationalSpace,MemSecondFrameGlue w → w∈rudvalisLattice)
    (v : RationalSpace) : distinguishedReflection v∈rudvalisLattice ↔ v∈rudvalisLattice := by
  obtain ⟨w,rfl⟩ := (rationalMonomialHom (codeP^4).val).surjective v
  rw [←distinguishedReflection_cyclic,←codeGroup_lattice_iff,
    secondFrameGlue_reflection_lattice_iff hEmbedding,codeGroup_lattice_iff]

theorem distinguishedReflection_basis (z : SeedCoordinate) :
    distinguishedReflection (secondFrame z)=
      if z.1=0 ∨ z.1=4 ∨ z.1=5 then secondFrame z else -secondFrame z := by
  change secondFrameReflection distinguishedSecondMask (secondFrame z)=_
  rw [←secondFrameBasis_apply,secondFrameReflection_basis]
  simp [distinguishedSecondMask,secondFrameBasis_apply]

theorem distinguishedReflection_ne_one : distinguishedReflection≠1 := by
  intro h
  have he := distinguishedReflection_basis (1,0)
  rw [h] at he
  have hn : secondFrame (1,0)= -secondFrame (1,0) := by simpa using he
  have hz : secondFrame (1,0)=0 := by
    ext i
    have hi := congrFun hn i
    change secondFrame (1,0) i=0
    change secondFrame (1,0) i= -secondFrame (1,0) i at hi
    linarith
  have hp := secondFrame_pairing (1,0) (1,0)
  rw [hz] at hp
  norm_num [rationalDot] at hp

theorem distinguishedReflection_order : orderOf distinguishedReflection=2 := by
  apply orderOf_eq_prime
  · apply LinearEquiv.ext
    intro v
    exact distinguishedReflection_involutive v
  · exact distinguishedReflection_ne_one

end Atlas.Rudvalis

