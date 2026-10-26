import Atlas.Rudvalis.FourCommonPerpendicular
import Atlas.Rudvalis.HeavyCommonPerpendicular

namespace Atlas.Rudvalis

theorem reference_common_perpendicular_card :
    Nat.card (CommonPerpendicularCrosses localReferenceCross referenceSecondCross)=730 := by
  change Nat.card {c : MinimalCross // CrossOrthogonal localReferenceCross c ∧ CrossOrthogonal referenceSecondCross c}=730
  rw [crossPiece_condition_card,coordinate_common_perpendicular_card,
    four_common_perpendicular_card,heavyCommonPerpendicularCrosses_card]

noncomputable def commonPerpendicularTransport (g : gaussianLatticeGroup) (x y : MinimalCross) :
    CommonPerpendicularCrosses x y ≃ CommonPerpendicularCrosses (g • x) (g • y) :=
  Equiv.subtypeEquiv (MulAction.toPerm g) (fun c =>
    and_congr (crossOrthogonal_gaussian g x c).symm (crossOrthogonal_gaussian g y c).symm)

theorem common_perpendicular_card (x y : MinimalCross) (hxy : CrossOrthogonal x y) :
    Nat.card (CommonPerpendicularCrosses x y)=730 := by
  let := rudvalis_generated_orthogonal_pairs_transitive
  let a : OrthogonalPairs := ⟨(localReferenceCross,referenceSecondCross),reference_crosses_orthogonal⟩
  let b : OrthogonalPairs := ⟨(x,y),hxy⟩
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq generatedGaussianGroup a b
  have hx : g.val • localReferenceCross=x := congrArg (fun z : OrthogonalPairs => z.val.1) hg
  have hy : g.val • referenceSecondCross=y := congrArg (fun z : OrthogonalPairs => z.val.2) hg
  rw [←hx,←hy,←Nat.card_congr (commonPerpendicularTransport g.val localReferenceCross referenceSecondCross)]
  exact reference_common_perpendicular_card

end Atlas.Rudvalis
