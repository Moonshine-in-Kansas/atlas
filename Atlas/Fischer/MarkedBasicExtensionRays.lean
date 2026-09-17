import Atlas.Fischer.MarkedBasicExtensionValues

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The image in actual normalized ray space of the marked common extensions. -/
def MarkedBasicExtensionRay (S : Finset Omega) :=
  Set.range (fun t : MarkedBasicExtension S => reflectingRootParameterRay t.val)

theorem markedBasicExtensionRay_card (S : Finset Omega) :
    Nat.card (MarkedBasicExtensionRay S) = Nat.card (MarkedBasicExtension S) := by
  exact (Nat.card_congr (Equiv.ofInjective
    (fun t : MarkedBasicExtension S => reflectingRootParameterRay t.val)
    (reflectingRootParameterRay_injective.comp Subtype.val_injective))).symm

theorem markedBasicExtensionRay_card_formula (S : Finset Omega) :
    Nat.card (MarkedBasicExtensionRay S) =
      (24 - S.card) + 32 * octadReplication S + 1024 * duadReplication S := by
  rw [markedBasicExtensionRay_card, markedBasicExtension_card_formula]

/-- The six source values for marked basic subsets, without homogeneity or any
Fischer group-order input. These count actual rays. -/
theorem markedBasicExtensionRay_card_values (S : Finset Omega) (s : Fin 6)
    (hS : S.card = s.val) :
    Nat.card (MarkedBasicExtensionRay S) = ![306936, 31671, 3510, 693, 180, 51] s := by
  rw [markedBasicExtensionRay_card]
  fin_cases s
  · exact markedBasicExtension_card_zero S hS
  · exact markedBasicExtension_card_one S hS
  · exact markedBasicExtension_card_two S hS
  · exact markedBasicExtension_card_three S hS
  · exact markedBasicExtension_card_four S hS
  · exact markedBasicExtension_card_five S hS

end Atlas.Fischer
