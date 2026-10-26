import Atlas.LinearGroups.ReeF4.WeylSL2Model
import Atlas.LinearGroups.SL2Order

/-! Order of the actual embedded fundamental SL₂ subgroup, transported through
its explicit faithful representation. No order of the ambient Ree model is used. -/
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem card_modelLongSL2Subgroup {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    Nat.card (modelLongSL2Subgroup hcard) = Nat.card F * (Nat.card F^2-1) := by
  rw [← Nat.card_congr (modelLongSL2Equiv hcard).toEquiv]
  exact Atlas.card_sl_two

theorem card_modelLongSL2Subgroup_primePower {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    Nat.card (modelLongSL2Subgroup hcard) = 2^(2*m+1) * ((2^(2*m+1))^2-1) := by
  rw [card_modelLongSL2Subgroup hcard, hcard]

end Atlas.ReeF4
