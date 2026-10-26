import Atlas.LinearGroups.ReeF4.WeylSL2Product
import Atlas.LinearGroups.SL2Order

/-! Local exact order of the faithfully embedded SL₂×F× subgroup.
This is not an order theorem for the whole Ree group or a full line stabilizer. -/
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem card_modelLongSL2ProductSubgroup {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    Nat.card (modelLongSL2ProductSubgroup hcard) =
      Nat.card F * (Nat.card F^2-1) * (Nat.card F-1) := by
  rw [← Nat.card_congr (modelLongSL2ProductEquiv hcard).toEquiv,
    Nat.card_prod, Atlas.card_sl_two, Nat.card_units]

theorem card_modelLongSL2ProductSubgroup_primePower {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    Nat.card (modelLongSL2ProductSubgroup hcard) =
      2^(2*m+1) * ((2^(2*m+1))^2-1) * (2^(2*m+1)-1) := by
  rw [card_modelLongSL2ProductSubgroup hcard, hcard]

end Atlas.ReeF4
