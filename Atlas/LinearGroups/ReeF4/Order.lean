import Atlas.LinearGroups.ReeF4.SpecialOppositePairCount
import Atlas.LinearGroups.ReeF4.OppositePairStabilizerOrder

/-! Full intrinsic Ree group order from counted opposite pairs and their
identified full stabilizer. Simplicity is not an input. -/
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem card_Model {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (Model F m) =
      (Nat.card F)^12 * ((Nat.card F)^6+1) * ((Nat.card F)^4-1) *
        ((Nat.card F)^3+1) * (Nat.card F-1) := by
  rw [model_order_oppositePair_factorization hcard,fullOppositePairStabilizer,
    card_fullOppositePairStabilizer hcard]
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hq4 : 1 ≤ (Nat.card F)^4 := pow_pos Nat.card_pos 4
  have hd : (Nat.card F)^4-1 =
      (Nat.card F-1)*(Nat.card F+1)*((Nat.card F)^2+1) := by
    zify [hq,hq4]
    ring
  rw [hd]
  ring

theorem card_Model_binary (hcard : Nat.card F=2^(2*0+1)) :
    Nat.card (Model F 0) = 35942400 := by
  rw [card_Model hcard,hcard]
  norm_num

end Atlas.ReeF4
