import Atlas.LinearGroups.ReeF4.RootSuzukiScalarProduct
import Atlas.LinearGroups.SuzukiFamily.Order

/-! Order of the actual embedded Suzuki × scalar subgroup. This does not
identify the full opposite-pair stabilizer or assert the full Ree order. -/
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem card_modelSuzukiProductSubgroup {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    Nat.card (modelSuzukiProductSubgroup hcard) =
      (Nat.card F)^2 * ((Nat.card F)^2+1) * (Nat.card F-1)^2 := by
  rw [← Nat.card_congr (modelSuzukiProductEquiv hcard).toEquiv,
    Nat.card_prod, Atlas.SuzukiFamily.card_group m hcard, Nat.card_units]
  ring

theorem card_modelSuzukiProductSubgroup_binary
    (hcard : Nat.card F = 2^(2*0+1)) :
    Nat.card (modelSuzukiProductSubgroup hcard) = 20 := by
  rw [card_modelSuzukiProductSubgroup hcard, hcard]
  norm_num

end Atlas.ReeF4
