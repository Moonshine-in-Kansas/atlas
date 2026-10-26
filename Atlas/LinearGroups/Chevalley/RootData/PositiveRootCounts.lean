import Atlas.LinearGroups.Chevalley.RootData.PositiveRootCard
import Atlas.LinearGroups.Chevalley.RootData.Counts
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-! Uniform positive-root counts for the existing nine coordinate root-data
providers. The total-root counts are reused unchanged. -/

noncomputable section
namespace Atlas.Chevalley
open Classical

/-- Cardinality of the exact positive-root filter used by the actual
root-inversion length package, for every existing uniform root-data provider. -/
theorem rootDatum_positive_root_filter_card (Φ : RootType) :
    (Finset.univ.filter (fun β : (rootDatum Φ).Root =>
      (rootDatum Φ).base.IsPos β)).card = Φ.positiveRootNumber := by
  have hpair := RootData.card_root_eq_two_mul_card_positive
    (rootDatum Φ).pairing (rootDatum Φ).base
  have htotal : Fintype.card (rootDatum Φ).Root = 2 * Φ.positiveRootNumber := by
    rw [← Nat.card_eq_fintype_card, rootDatum_root_card]
  omega

/-- The subtype of actual positive root labels has the specified cardinality;
no choice of representatives or separate table is introduced. -/
theorem rootDatum_positive_root_card (Φ : RootType) :
    Nat.card {β : (rootDatum Φ).Root // (rootDatum Φ).base.IsPos β} =
      Φ.positiveRootNumber := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    rootDatum_positive_root_filter_card]

end Atlas.Chevalley
