import Atlas.Fischer.MarkedBasicExtensionCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem markedBasicExtension_card_zero (S : Finset Omega) (hS : S.card = 0) :
    Nat.card (MarkedBasicExtension S) = 306936 := by
  rw [markedBasicExtension_card_formula, octadReplication_zero S hS,
    duadReplication_small S (by omega), hS]
  norm_num [Nat.choose_two_right]

theorem markedBasicExtension_card_one (S : Finset Omega) (hS : S.card = 1) :
    Nat.card (MarkedBasicExtension S) = 31671 := by
  rw [markedBasicExtension_card_formula, octadReplication_one S hS,
    duadReplication_small S (by omega), hS]
  norm_num

theorem markedBasicExtension_card_two (S : Finset Omega) (hS : S.card = 2) :
    Nat.card (MarkedBasicExtension S) = 3510 := by
  rw [markedBasicExtension_card_formula, octadReplication_two S hS,
    duadReplication_small S (by omega), hS]
  norm_num

theorem markedBasicExtension_card_three (S : Finset Omega) (hS : S.card = 3) :
    Nat.card (MarkedBasicExtension S) = 693 := by
  rw [markedBasicExtension_card_formula, octadReplication_three S hS,
    duadReplication_large S (by omega), hS]

theorem markedBasicExtension_card_four (S : Finset Omega) (hS : S.card = 4) :
    Nat.card (MarkedBasicExtension S) = 180 := by
  rw [markedBasicExtension_card_formula, octadReplication_four S hS,
    duadReplication_large S (by omega), hS]

theorem markedBasicExtension_card_five (S : Finset Omega) (hS : S.card = 5) :
    Nat.card (MarkedBasicExtension S) = 51 := by
  rw [markedBasicExtension_card_formula, octadReplication_five S hS,
    duadReplication_large S (by omega), hS]

end Atlas.Fischer
