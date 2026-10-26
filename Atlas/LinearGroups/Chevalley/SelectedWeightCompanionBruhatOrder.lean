import Atlas.LinearGroups.Chevalley.WeightCompanionBruhatOrder
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion
import Atlas.LinearGroups.Chevalley.RootData.PositiveRootCounts

/-! The actual all-type companion order as a Weyl length sum. Evaluation
of that sum by the fundamental-degree product remains a separate theorem. -/
noncomputable section
namespace Atlas.Chevalley
open Classical RootData

theorem selectedWeightCompanion_card_eq_weylSum (Φ : RootType)
    (K : Type*) [Field K] [Finite K] :
    Nat.card (SelectedWeightCompanion Φ K) =
      Nat.card K ^ Φ.positiveRootNumber * (Nat.card K - 1) ^ Φ.rank *
        rootWeylPoincareEval (rootDatum Φ).pairing (rootDatum Φ).base (Nat.card K) := by
  have h := weightCompanion_card_eq_spanning_weylSum
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) K
    (rootDatum_simpleDiamondProducts Φ) (selectedWeightSet_spans Φ)
  simpa only [rootDatum_positive_root_card, model_base_card] using h

end Atlas.Chevalley
