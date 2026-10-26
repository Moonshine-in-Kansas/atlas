import Atlas.LinearGroups.ReeF4.RootSuzukiLeviGroup
import Atlas.LinearGroups.SuzukiFamily.Order

/-! Exact order of the actual local Suzuki subgroup, transferred only after
its faithful full-coordinate identification. Independent of simplicity. -/
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem card_suzukiLeviSubgroup (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Nat.card (suzukiLeviSubgroup m hcard) =
      (Nat.card F)^2*((Nat.card F)^2+1)*(Nat.card F-1) := by
  rw [← Nat.card_congr (suzukiLeviEquivalence m hcard).toEquiv]
  exact Atlas.SuzukiFamily.card_group m hcard

theorem card_suzukiLeviSubgroup_binary (hcard : Nat.card F = 2^(2*0+1)) :
    Nat.card (suzukiLeviSubgroup 0 hcard) = 20 := by
  rw [card_suzukiLeviSubgroup, hcard]
  norm_num

end Atlas.ReeF4
