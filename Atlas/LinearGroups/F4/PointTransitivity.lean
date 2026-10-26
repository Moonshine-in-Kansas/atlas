import Atlas.LinearGroups.F4.PointOpenNormalize
import Atlas.LinearGroups.F4.OppositeCellTransitivity

/-! Transitivity from explicit chart reduction and actual root transformations.
No full-group or stabilizer cardinality is used. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F]

theorem whiteZero_vector_from_opposite (x : Carrier F) (hx : x≠0)
    (ha : adjoint x=0) (ht : trace x=0) :
    ∃ g : Model F, g.val (0,![0,0,![0,0,0,0,0,0,0,1]])=x := by
  obtain ⟨h,y,hy⟩ := whiteZero_move_into_oppositeCell x hx ha ht
  obtain ⟨k,hk⟩ := oppositeCell_from_base y
  refine ⟨h⁻¹*k,?_⟩
  change h.val.symm (k.val _)=x
  rw [hk,←hy]
  exact h.val.symm_apply_apply x

theorem whiteZero_vectors_transitive (x y : Carrier F)
    (hx : x≠0) (ha : adjoint x=0) (ht : trace x=0)
    (hy : y≠0) (hb : adjoint y=0) (hu : trace y=0) :
    ∃ g : Model F, g.val x=y := by
  obtain ⟨g,hg⟩ := whiteZero_vector_from_opposite x hx ha ht
  obtain ⟨h,hh⟩ := whiteZero_vector_from_opposite y hy hb hu
  refine ⟨h*g⁻¹,?_⟩
  change h.val (g.val.symm x)=y
  rw [←hg,g.val.symm_apply_apply,hh]

instance whiteZeroPoints_pretransitive : MulAction.IsPretransitive (Model F) (WhiteZeroPoints F) where
  exists_smul_eq x y := by
    obtain ⟨g,hg⟩ := whiteZero_vectors_transitive x.val.rep y.val.rep
      (Projectivization.rep_nonzero _) x.prop.2 x.prop.1
      (Projectivization.rep_nonzero _) y.prop.2 y.prop.1
    refine ⟨g,Subtype.ext ?_⟩
    change g.val • x.val=y.val
    rw [←Projectivization.mk_rep x.val,Projectivization.smul_mk]
    simp only [LinearEquiv.smul_def]
    simpa only [hg] using Projectivization.mk_rep y.val

theorem whiteZeroPoints_transitive : MulAction.IsPretransitive (Model F) (WhiteZeroPoints F) :=
  inferInstance

end Atlas.F4
