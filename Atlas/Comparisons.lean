import Atlas.Comparisons.CatalogueCardinality
import Atlas.Comparisons.CatalogueSameLabel
import Atlas.Comparisons.CatalogueObstructions

/-! # The main comparison theorem for the completed ATLAS catalogue

The entries contain actual finite-field and extension presentations and the
retained concrete group models. The public statement classifies group
isomorphisms, not equality of numerical order formulas. Order bridges, explicit
normalization maps, and the two equal-order non-isomorphism obstructions are
proved separately and combined here.

Coverage is the canonical simple ranges of the 13 completed families and the
17 fixed constructions (16 sporadics and Tits). Canonical Mathieu markings are
used. Existing lower-rank/derived comparison interfaces remain available in
other Atlas.Comparisons modules, without claiming unfinished identifications.
-/
namespace Atlas.Comparisons.Catalogue
open Atlas.OrderArithmetic

/-- Equal normalized labels give an actual group isomorphism, by composing
proved normalization maps and actual field/extension transport. -/
theorem isomorphic_of_normalized_label_eq (x y : Entry)
    (h : OrderArithmetic.normalize (label x) = OrderArithmetic.normalize (label y)) :
    Nonempty (Model x ≃* Model y) := by
  have hl : label (normalizedEntry x) = label (normalizedEntry y) := by
    rw [normalizedEntry_label, normalizedEntry_label, h]
  obtain ⟨e⟩ := same_label_equiv (normalizedEntry x) (normalizedEntry y) hl
  exact ⟨(normalizeEquiv x).trans (e.trans (normalizeEquiv y).symm)⟩

/-- An isomorphism between actual catalogue groups forces equality of the
normalized labels. The two genuine numerical collision patterns are excluded
by proved structural invariants, not by order alone. -/
theorem normalized_label_eq_of_isomorphic (x y : Entry)
    (h : Nonempty (Model x ≃* Model y)) :
    OrderArithmetic.normalize (label x) = OrderArithmetic.normalize (label y) := by
  obtain ⟨e⟩ := h
  have hc : order (label x) = order (label y) := by
    rw [← card x, ← card y]
    exact Nat.card_congr e.toEquiv
  rcases (catalogue_order_eq_iff (admissible x) (admissible y)).mp hc with he | he
  · exact he
  · have he' : OrderArithmetic.Exceptional (label (normalizedEntry x))
        (label (normalizedEntry y)) := by
      simpa only [normalizedEntry_label] using he
    exact (exceptional_not_isomorphic (normalizedEntry x) (normalizedEntry y) he'
      ⟨(normalizeEquiv x).symm.trans (e.trans (normalizeEquiv y))⟩).elim

/-- Main actual-group comparison theorem. Its only arguments are the two
well-formed completed catalogue entries; it assumes no order formula,
comparison certificate, simplicity theorem or group-recognition hypothesis. -/
theorem isomorphic_iff_normalized_label_eq (x y : Entry) :
    Nonempty (Model x ≃* Model y) ↔
      OrderArithmetic.normalize (label x) = OrderArithmetic.normalize (label y) :=
  ⟨normalized_label_eq_of_isomorphic x y, isomorphic_of_normalized_label_eq x y⟩

/-- All different normalized catalogue entries are nonisomorphic, including
the equal-order A8/L3(4) and odd B/C pairs. -/
theorem not_isomorphic_of_normalized_label_ne (x y : Entry)
    (h : OrderArithmetic.normalize (label x) ≠ OrderArithmetic.normalize (label y)) :
    ¬ Nonempty (Model x ≃* Model y) :=
  fun he => h ((isomorphic_iff_normalized_label_eq x y).mp he)

end Atlas.Comparisons.Catalogue
