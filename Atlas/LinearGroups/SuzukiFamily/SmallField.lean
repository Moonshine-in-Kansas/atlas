import Atlas.LinearGroups.SuzukiFamily.Order
import Atlas.GroupTheory.OrderTwentyNotSimple

/-! Nonsimplicity at q=2 for the same generated matrix model. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem binary_not_simple (hcard : Nat.card F=2) : ¬ IsSimpleGroup (Group F 0) :=
  Atlas.GroupTheory.not_simple_of_card_twenty (card_group_binary hcard)
end Atlas.SuzukiFamily
