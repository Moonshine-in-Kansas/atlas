import Atlas.LinearGroups.SuzukiFamily.Bruhat
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-! Uniform order from the unique matrix Bruhat cells, independently of simplicity. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem card_group (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Nat.card (Group F m) = (Nat.card F)^2*((Nat.card F)^2+1)*(Nat.card F-1) := by
  rw [← Nat.card_congr (cellEquiv m hcard)]
  simp only [CellParameters,Nat.card_sum,Nat.card_prod,Nat.card_units]
  ring

theorem card_group_binary (hcard : Nat.card F=2) : Nat.card (Group F 0)=20 := by
  have hc : Nat.card F=2^(2*0+1) := by simpa using hcard
  rw [card_group 0 hc,hcard]
  norm_num

theorem card_group_eight (hcard : Nat.card F=8) : Nat.card (Group F 1)=29120 := by
  have hc : Nat.card F=2^(2*1+1) := by simpa using hcard
  rw [card_group 1 hc,hcard]
  norm_num

theorem card_group_thirtyTwo (hcard : Nat.card F=32) : Nat.card (Group F 2)=32537600 := by
  have hc : Nat.card F=2^(2*2+1) := by simpa using hcard
  rw [card_group 2 hc,hcard]
  norm_num

theorem card_group_oneTwentyEight (hcard : Nat.card F=128) :
    Nat.card (Group F 3)=34093383680 := by
  have hc : Nat.card F=2^(2*3+1) := by simpa using hcard
  rw [card_group 3 hc,hcard]
  norm_num
end Atlas.SuzukiFamily
