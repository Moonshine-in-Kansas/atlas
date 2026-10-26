import Atlas.Rudvalis.SecondFrameGlueDual
import Atlas.Rudvalis.SecondFrameProjection

namespace Atlas.Rudvalis
open scoped BigOperators

noncomputable def frameGlueMask : Finset SeedCoordinate := Finset.univ.image frameGlueSeedCoordinate

noncomputable def frameGlueProjection : RationalSpace →ₗ[ℚ] RationalSpace :=
  secondFrameProjection frameGlueMask

noncomputable def frameGlueReflection : RationalSpace ≃ₗ[ℚ] RationalSpace :=
  secondFrameReflection frameGlueMask

theorem frameGlueEmbedding_repr (y : FrameGlueCoordinate→ℚ) (i : SeedCoordinate) :
    secondFrameBasis.repr (frameGlueEmbedding y) i=
      ∑j : FrameGlueCoordinate,if frameGlueSeedCoordinate j=i then y j/2 else 0 := by
  simp only [frameGlueEmbedding,LinearMap.coe_mk,AddHom.coe_mk,←secondFrameBasis_apply,
    map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,Module.Basis.repr_self,
    Finsupp.single_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp_all

theorem frameGlueProjection_coordinates (v : RationalSpace) :
    frameGlueProjection v=frameGlueEmbedding
      (fun j => 2*secondFrameBasis.repr v (frameGlueSeedCoordinate j)) := by
  classical
  apply secondFrameBasis.repr.injective
  ext i
  change secondFrameBasis.repr (secondFrameProjection frameGlueMask v) i=_
  rw [secondFrameProjection_repr,frameGlueEmbedding_repr]
  by_cases hi : i∈frameGlueMask
  · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    simp only [hi,ite_true,frameGlueSeedCoordinate_injective.eq_iff]
    simp
  · simp only [hi,ite_false]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hn : frameGlueSeedCoordinate j≠i := by
      intro he
      apply hi
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,he⟩
    simp [hn]

theorem frameGlueProjection_embedding (y : FrameGlueCoordinate→ℚ) :
    frameGlueProjection (frameGlueEmbedding y)=frameGlueEmbedding y := by
  classical
  apply (secondFrameProjection_eq_self_iff frameGlueMask _).mpr
  intro i hi
  rw [frameGlueEmbedding_repr]
  apply Finset.sum_eq_zero
  intro j _
  have hn : frameGlueSeedCoordinate j≠i := by
    intro he
    exact hi (Finset.mem_image.mpr ⟨j,Finset.mem_univ j,he⟩)
  simp [hn]

theorem frameGlueProjection_range : frameGlueProjection.range=frameGlueEmbedding.range := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨_,(frameGlueProjection_coordinates w).symm⟩
  · rintro ⟨y,rfl⟩
    exact ⟨_,frameGlueProjection_embedding y⟩

theorem frameGlueProjection_glue (v : RationalSpace) (hv : MemSecondFrameGlue v) :
    frameGlueProjection v=v := by
  obtain ⟨z,hz,rfl⟩ := hv
  exact frameGlueProjection_embedding _

/-- Conditional only on the as-yet separate actual lattice embedding of local glue. -/
theorem secondFrameGlue_reflection_preserves
    (hEmbedding : ∀w : RationalSpace,MemSecondFrameGlue w → w∈rudvalisLattice)
    (v : RationalSpace) (hv : v∈rudvalisLattice) : frameGlueReflection v∈rudvalisLattice := by
  have hp : MemSecondFrameGlueDual (frameGlueProjection v) := by
    refine ⟨?_,?_⟩
    · rw [←frameGlueProjection_range]
      exact ⟨v,rfl⟩
    · intro w hw
      change ∃k : ℤ,rationalDot (secondFrameProjection frameGlueMask v) w=k
      rw [secondFrameProjection_selfadjoint]
      change ∃k : ℤ,rationalDot v (frameGlueProjection w)=k
      rw [frameGlueProjection_glue w hw]
      exact rudvalisLattice_integral v w hv (hEmbedding w hw)
  have hm := (secondFrameGlue_dual_iff_twice_mem _).mp hp
  exact rudvalisLattice.sub_mem (hEmbedding _ hm) hv

theorem secondFrameGlue_reflection_lattice_iff
    (hEmbedding : ∀w : RationalSpace,MemSecondFrameGlue w → w∈rudvalisLattice)
    (v : RationalSpace) : frameGlueReflection v∈rudvalisLattice ↔ v∈rudvalisLattice := by
  constructor
  · intro h
    have hh := secondFrameGlue_reflection_preserves hEmbedding (frameGlueReflection v) h
    change secondFrameReflection frameGlueMask (secondFrameReflection frameGlueMask v)∈rudvalisLattice at hh
    rwa [secondFrameReflection_involutive frameGlueMask v] at hh
  · exact secondFrameGlue_reflection_preserves hEmbedding v

end Atlas.Rudvalis
