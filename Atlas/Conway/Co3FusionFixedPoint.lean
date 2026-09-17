import Atlas.Conway.Co3ActionTransitivity
import Atlas.Conway.OrthogonalPairSigns

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000

def co3BasePoint : Mathieu23Points co3MarkedCoordinate :=
  ⟨((0,0),1),by change ((0,0),1) ≠ co3MarkedCoordinate; decide⟩

theorem co3Fusion_base_input :
    (signIsometry co3FusionSignCode * zeta).val
      (minimumPairPlus co3MarkedCoordinate co3BasePoint.val) =
      -minimumPairPlus ((0,0),2) ((0,0),3) := by
  apply Subtype.ext
  apply rationalEmbedding_injective
  change rationalEmbedding (signChange co3FusionSignCode.val
    (zeta.val (minimumPairPlus co3MarkedCoordinate co3BasePoint.val)).val) = _
  rw [rationalEmbedding_signChange,zeta_agrees,co3FusionSignCode_val]
  decide +kernel

theorem co3Fusion_fixes_base_endpoint (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a) :
    (co3FusionIsometry p).val (minimumPairPlus co3MarkedCoordinate co3BasePoint.val) =
      minimumPairPlus co3MarkedCoordinate co3BasePoint.val := by
  have hm : (permutationEmbedding p).val ((signIsometry co3FusionSignCode * zeta).val
      (minimumPairPlus co3MarkedCoordinate co3BasePoint.val)) =
      (signIsometry co3FusionSignCode * zeta).val
      (minimumPairPlus co3MarkedCoordinate co3BasePoint.val) := by
    rw [co3Fusion_base_input,map_neg,(permutation_minimumPair p _ _).1,
      hp _ (by simp [co3FusionTriple]),hp _ (by simp [co3FusionTriple])]
  change zeta.val ((signIsometry co3FusionSignCode).val ((permutationEmbedding p).val
    ((signIsometry co3FusionSignCode * zeta).val (minimumPairPlus co3MarkedCoordinate co3BasePoint.val)))) = _
  rw [hm]
  have hs : (signIsometry co3FusionSignCode).val ((signIsometry co3FusionSignCode * zeta).val
      (minimumPairPlus co3MarkedCoordinate co3BasePoint.val)) =
      zeta.val (minimumPairPlus co3MarkedCoordinate co3BasePoint.val) := by
    apply Subtype.ext
    exact signChange_involutive _ _
  rw [hs]
  exact congrArg (fun g : LeechIsometryGroup => g.val (minimumPairPlus co3MarkedCoordinate co3BasePoint.val)) zeta_sq

theorem co3Fusion_fixes_base_decomposition (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a) :
    (⟨co3FusionIsometry p,co3Fusion_fixes_normSix p hp⟩ : Co3MarkedModel) •
      co3PointHeptadDecompositionEquiv _ (Sum.inl co3BasePoint) =
      co3PointHeptadDecompositionEquiv _ (Sum.inl co3BasePoint) := by
  apply Subtype.ext
  change ({minimumPairPlus co3MarkedCoordinate co3BasePoint.val,
    normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate co3BasePoint.val} : Finset leech).image
      (co3FusionIsometry p).val = _
  simp [map_sub,co3Fusion_fixes_normSix p hp,co3Fusion_fixes_base_endpoint p hp]
  rfl

end Atlas.Conway
