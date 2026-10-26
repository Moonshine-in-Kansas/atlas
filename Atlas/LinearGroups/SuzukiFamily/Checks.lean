import Atlas.LinearGroups.SuzukiFamily.SplitBorel
import Atlas.LinearGroups.SuzukiFamily.ExactSimplicity

/-! Small-parameter regressions by specialization of uniform structural theorems. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem checks_binary (hc : Nat.card F=2) :
    Nat.card (pointSet (F := F) 0)=5 ∧
    Nat.card (rootSubgroup 0 (show Nat.card F=2^(2*0+1) by simpa using hc))=4 ∧
    Nat.card (torusSubgroup (F := F) 0)=1 ∧
    Nat.card (borel 0 (show Nat.card F=2^(2*0+1) by simpa using hc))=4 := by
  rw [card_pointSet,card_rootSubgroup,card_torusSubgroup,card_borel,hc]
  norm_num

theorem checks_eight (hc : Nat.card F=8) :
    Nat.card (pointSet (F := F) 1)=65 ∧
    Nat.card (rootSubgroup 1 (show Nat.card F=2^(2*1+1) by simpa using hc))=64 ∧
    Nat.card (torusSubgroup (F := F) 1)=7 ∧
    Nat.card (borel 1 (show Nat.card F=2^(2*1+1) by simpa using hc))=448 := by
  rw [card_pointSet,card_rootSubgroup,card_torusSubgroup,card_borel,hc]
  norm_num

theorem checks_thirtyTwo (hc : Nat.card F=32) :
    Nat.card (pointSet (F := F) 2)=1025 ∧
    Nat.card (rootSubgroup 2 (show Nat.card F=2^(2*2+1) by simpa using hc))=1024 ∧
    Nat.card (torusSubgroup (F := F) 2)=31 ∧
    Nat.card (borel 2 (show Nat.card F=2^(2*2+1) by simpa using hc))=31744 := by
  rw [card_pointSet,card_rootSubgroup,card_torusSubgroup,card_borel,hc]
  norm_num

theorem checks_oneTwentyEight (hc : Nat.card F=128) :
    Nat.card (pointSet (F := F) 3)=16385 ∧
    Nat.card (rootSubgroup 3 (show Nat.card F=2^(2*3+1) by simpa using hc))=16384 ∧
    Nat.card (torusSubgroup (F := F) 3)=127 ∧
    Nat.card (borel 3 (show Nat.card F=2^(2*3+1) by simpa using hc))=2080768 := by
  rw [card_pointSet,card_rootSubgroup,card_torusSubgroup,card_borel,hc]
  norm_num

end Atlas.SuzukiFamily
