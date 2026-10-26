import Atlas.Rudvalis.ReferenceHeavyOrbit
import Atlas.Rudvalis.FourLocalCrossOrbit
import Atlas.Rudvalis.ConditionalGlobalTransitivity

namespace Atlas.Rudvalis

theorem reference_four_cross_transitive (v w : FourBlockCrosses)
    (hv : CrossOrthogonal localReferenceCross (shellPieceCrossMap fourShellPiece v))
    (hw : CrossOrthogonal localReferenceCross (shellPieceCrossMap fourShellPiece w)) :
    ∃g : codeReferenceStabilizer,g.val • shellPieceCrossMap fourShellPiece v=shellPieceCrossMap fourShellPiece w := by
  rw [localReferenceCross_eq] at hv hw
  obtain ⟨g,hg,h⟩ := fourLocal_crosses_transitive v w hv hw
  refine ⟨⟨g,?_⟩,h⟩
  change g • localReferenceCross=localReferenceCross
  rw [localReferenceCross_eq]
  exact hg

theorem localFusion_orbit_sizes :
    Nat.card (MulAction.orbit localFusionGroup localThirdCross)=27 ∨
    Nat.card (MulAction.orbit localFusionGroup localThirdCross)=219 ∨
    Nat.card (MulAction.orbit localFusionGroup localThirdCross)=1563 ∨
    Nat.card (MulAction.orbit localFusionGroup localThirdCross)=1755 :=
  localFusion_orbit_sizes_of_piece_transitivity reference_four_cross_transitive reference_heavy_cross_transitive

/-- The actual local group is transitive on the complete orthogonal shell,
with all geometric hypotheses discharged. -/
theorem localFusionGroup_orthogonal_orbit :
    MulAction.orbit localFusionGroup localThirdCross=
      {c : MinimalCross | CrossOrthogonal localReferenceCross c} :=
  localFusionGroup_full_orthogonal_orbit localFusion_orbit_sizes

theorem rudvalis_generated_cross_transitive :
    MulAction.IsPretransitive generatedGaussianGroup MinimalCross :=
  generated_cross_pretransitive localFusion_orbit_sizes

theorem rudvalis_orthogonal_degree (x : MinimalCross) :
    Nat.card (OrthogonalCrosses x)=1755 :=
  generated_uniform_orthogonal_degree localFusion_orbit_sizes x

theorem rudvalis_generated_orthogonal_pairs_transitive :
    MulAction.IsPretransitive generatedGaussianGroup OrthogonalPairs :=
  generated_orthogonal_pairs_pretransitive localFusion_orbit_sizes

theorem rudvalis_ordered_orthogonal_pairs_card : Nat.card OrthogonalPairs=7125300 :=
  generated_ordered_orthogonal_pairs_card localFusion_orbit_sizes

end Atlas.Rudvalis

