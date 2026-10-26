import Atlas.Rudvalis.DistinguishedReflection

namespace Atlas.Rudvalis

def secondFrameLineMask (a : Point) : Finset SeedCoordinate :=
  Finset.univ.filter (fun z => dot a.val (rowLabel z.1).val=0)

def secondFrameLineShift (r : Fin 7) : Fin 7 := ![1,4,6,2,3,0,5] r

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem secondFrameLineShift_certificate (r : Fin 7) (z : SeedCoordinate) :
    dot (rowLabel r).val (rowLabel z.1).val=0 ↔
      ∃i : Fin 3,frameGluePoint i=rowLabel
        (((secondFrameCyclicPerm^(secondFrameLineShift r).val).symm z).1) := by
  decide +kernel +revert

theorem secondFrameLineMask_cyclic (a : Point) : ∃n : Fin 7,secondFrameLineMask a=
    frameGlueMask.map (secondFrameCyclicPerm^n.val).toEmbedding := by
  obtain ⟨r,rfl⟩ := rowLabel_bijective.surjective a
  refine ⟨secondFrameLineShift r,?_⟩
  ext z
  rw [Finset.mem_map_equiv,frameGlueMask_mem_iff_row]
  simp only [secondFrameLineMask,Finset.mem_filter,Finset.mem_univ,true_and]
  exact secondFrameLineShift_certificate r z

noncomputable def secondFrameLineReflection (a : Point) : RationalSpace ≃ₗ[ℚ] RationalSpace :=
  secondFrameReflection (secondFrameLineMask a)

theorem secondFrameLineReflection_pairing (a : Point) (v w : RationalSpace) :
    rationalDot (secondFrameLineReflection a v) (secondFrameLineReflection a w)=rationalDot v w :=
  secondFrameReflection_pairing (secondFrameLineMask a) v w

theorem secondFrameLineReflection_gaussian (a : Point) (v : RationalSpace) :
    secondFrameLineReflection a (rationalI v)=rationalI (secondFrameLineReflection a v) := by
  obtain ⟨n,hn⟩ := secondFrameLineMask_cyclic a
  obtain ⟨w,rfl⟩ := (rationalMonomialHom (codeP^n.val).val).surjective v
  change secondFrameReflection (secondFrameLineMask a) _=rationalI (secondFrameReflection (secondFrameLineMask a) _)
  rw [hn,←codeGroup_rational_gaussian_linear,←secondFrameReflection_cyclic,
    ←secondFrameReflection_cyclic]
  change rationalMonomialHom (codeP^n.val).val (frameGlueReflection (rationalI w))=
    rationalI (rationalMonomialHom (codeP^n.val).val (frameGlueReflection w))
  rw [frameGlueReflection_gaussian,codeGroup_rational_gaussian_linear]

theorem secondFrameLineReflection_lattice_of_glue_embedding
    (hEmbedding : ∀w : RationalSpace,MemSecondFrameGlue w → w∈rudvalisLattice)
    (a : Point) (v : RationalSpace) : secondFrameLineReflection a v∈rudvalisLattice ↔ v∈rudvalisLattice := by
  obtain ⟨n,hn⟩ := secondFrameLineMask_cyclic a
  obtain ⟨w,rfl⟩ := (rationalMonomialHom (codeP^n.val).val).surjective v
  change secondFrameReflection (secondFrameLineMask a) _∈rudvalisLattice ↔ _
  rw [hn,←secondFrameReflection_cyclic,←codeGroup_lattice_iff]
  exact (secondFrameGlue_reflection_lattice_iff hEmbedding w).trans (codeGroup_lattice_iff (codeP^n.val) w)

end Atlas.Rudvalis
