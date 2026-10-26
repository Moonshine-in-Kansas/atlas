import Atlas.GroupTheory.OrderSixTwelveNotSimple
import Atlas.LinearGroups.Chevalley.ModelAOrder

/-! Nonsimplicity of the actual uniform A1 model over fields of orders two
and three. The obstruction uses genuine small-index Sylow subgroups and the
independently proved actual-model order, without an older PSL comparison. -/
noncomputable section
namespace Atlas.Chevalley

theorem model_A_one_two_not_simple (K : Type*) [Field K] [Finite K]
    (hq : Nat.card K = 2) : ¬ IsSimpleGroup (Model (.A 1 (by decide)) K) := by
  apply Atlas.GroupTheory.not_simple_of_card_six
  rw [model_A_card, hq]
  norm_num

theorem model_A_one_three_not_simple (K : Type*) [Field K] [Finite K]
    (hq : Nat.card K = 3) : ¬ IsSimpleGroup (Model (.A 1 (by decide)) K) := by
  apply Atlas.GroupTheory.not_simple_of_card_twelve
  rw [model_A_card, hq]
  norm_num

end Atlas.Chevalley
