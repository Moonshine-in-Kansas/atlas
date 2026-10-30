import Atlas.LinearGroups.ReeF4.OppositePairStabilizer
import Atlas.LinearGroups.ReeF4.RootSuzukiScalarOrder

/-! Order transferred only after both full-stabilizer inclusions were proved. -/
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem card_fullOppositePairStabilizer {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (MulAction.stabilizer (Model F m) (baseSpecialOppositePair (F := F) m)) =
      (Nat.card F)^2*((Nat.card F)^2+1)*(Nat.card F-1)^2 := by
  rw [←oppositePairStabilizer_eq_suzukiProduct hcard]
  exact card_modelSuzukiProductSubgroup hcard

end Atlas.ReeF4
