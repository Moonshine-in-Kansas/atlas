import Atlas.Fischer.CubicQuadrilateralHistogram

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def cubicQuadrilateralPairPerm (D : Octad) (g : MathieuOctadStabilizer D) :
    Equiv.Perm (Octad × Octad) :=
  Equiv.prodCongr (MulAction.toPerm g.val) (MulAction.toPerm g.val)

 theorem cubicQuadrilateral_pair_incidence_invariant (D : Octad) :
    CubicOctadCoordinateInvariant D (fun p => ∑ a : Octad × Octad,
      cubicQuadrilateralNormalizedWeight D a.1 a.2 *
        cubicPointOctadIncidence p (cubicQuadrilateralLabel a.1 a.2)) := by
  apply cubicWeightedIncidence_invariant D
    (fun a : Octad × Octad => cubicQuadrilateralLabel a.1 a.2)
    (fun a : Octad × Octad => cubicQuadrilateralNormalizedWeight D a.1 a.2)
    (cubicQuadrilateralPairPerm D)
  · intro g a
    exact cubicQuadrilateralLabel_smul g.val a.1 a.2
  · intro g a
    have hg : g.val • D = D := g.property
    have h := cubicQuadrilateralNormalizedWeight_smul g.val D a.1 a.2
    rw [hg] at h
    exact h

 theorem cubicQuadrilateral_inside_point_sum (D : Octad) (i : OctadInterior D) :
    (∑ F : Octad,∑ G : Octad,cubicQuadrilateralNormalizedWeight D F G *
      cubicPointOctadIncidence i.val (cubicQuadrilateralLabel F G)) = 36090 := by
  have h := cubicWeightedIncidence_inside D
    (fun a : Octad × Octad => cubicQuadrilateralLabel a.1 a.2)
    (fun a : Octad × Octad => cubicQuadrilateralNormalizedWeight D a.1 a.2)
    (cubicQuadrilateral_pair_incidence_invariant D) i
  simp only [Fintype.sum_prod_type] at h
  rw [cubicQuadrilateral_weight_first_moment,cubicQuadrilateral_weight_total] at h
  norm_num at h
  exact h

 theorem cubicQuadrilateral_outside_point_sum (D : Octad) (i : OctadExterior D) :
    (∑ F : Octad,∑ G : Octad,cubicQuadrilateralNormalizedWeight D F G *
      cubicPointOctadIncidence i.val (cubicQuadrilateralLabel F G)) = -13710 := by
  have h := cubicWeightedIncidence_outside D
    (fun a : Octad × Octad => cubicQuadrilateralLabel a.1 a.2)
    (fun a : Octad × Octad => cubicQuadrilateralNormalizedWeight D a.1 a.2)
    (cubicQuadrilateral_pair_incidence_invariant D) i
  simp only [Fintype.sum_prod_type] at h
  rw [cubicQuadrilateral_weight_first_moment,cubicQuadrilateral_weight_total] at h
  norm_num at h
  exact h

/-- The point-refined signed sum is derived from the actual octad stabilizer
and the proved signed histogram. -/
theorem cubicQuadrilateral_point_sum (D : Octad) (i : Omega) :
    (∑ F : Octad,∑ G : Octad,cubicQuadrilateralNormalizedWeight D F G *
      cubicPointOctadIncidence i (cubicQuadrilateralLabel F G)) =
      if i ∈ D.val then 36090 else -13710 := by
  by_cases hi : i ∈ D.val
  · rw [if_pos hi]
    exact cubicQuadrilateral_inside_point_sum D ⟨i,hi⟩
  · rw [if_neg hi]
    exact cubicQuadrilateral_outside_point_sum D ⟨i,hi⟩

end Atlas.Fischer
