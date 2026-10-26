import Atlas.Comparisons.CatalogueModels
import Atlas.Comparisons.Cardinality
import Atlas.OrderArithmetic.Classification

namespace Atlas.Comparisons.Catalogue
open Atlas.OrderArithmetic

theorem Fixed.card (x : Fixed) : Nat.card x.Model = order (.fixed x.label) := by
  cases x with
  | M11 => exact CatalogueOrders.M11_card _ _
  | M12 => exact CatalogueOrders.M12_card _
  | M22 => exact CatalogueOrders.M22_card _ _
  | M23 => exact CatalogueOrders.M23_card _
  | M24 => exact CatalogueOrders.M24_card
  | Co1 => exact CatalogueOrders.Co1_card
  | Co2 => exact CatalogueOrders.Co2_card
  | Co3 => exact CatalogueOrders.Co3_card
  | McL => exact CatalogueOrders.McL_card
  | HS => exact CatalogueOrders.HS_card
  | Suz => exact CatalogueOrders.Suz_card
  | J2 => exact CatalogueOrders.J2_card
  | Fi22 => exact CatalogueOrders.Fi22_card
  | Fi23 => exact CatalogueOrders.Fi23_card
  | Fi24prime => exact CatalogueOrders.Fi24prime_card
  | Ru => exact CatalogueOrders.Ru_card
  | Tits => exact CatalogueOrders.Tits_card

/-- The order bridge is proved for every entry, not supplied as a registry assumption. -/
theorem card (x : Entry) : Nat.card (Model x) = order (label x) := by
  cases x with
  | cyclic p hp => exact CatalogueOrders.cyclic_card p hp.pos
  | alternating n hn => exact CatalogueOrders.alternating_card n (by omega)
  | linear F d h =>
    letI : NeZero d := ⟨by have := h.1; omega⟩
    exact CatalogueOrders.linear_card F.carrier d
  | unitary E d h => exact CatalogueOrders.unitary_card _ _ E.finrank d (by have := h.1; omega)
  | B F r h => exact CatalogueOrders.B_card _ r (by have := h.1; omega)
  | C F r h => exact CatalogueOrders.symplectic_card _ r (by have := h.1; omega)
  | Dplus F r h => exact CatalogueOrders.Dplus_card _ r h.1
  | Dminus E r h => exact CatalogueOrders.Dminus_card _ _ E.finrank r (by have := h.1; omega)
  | G2 F h => exact CatalogueOrders.G2_card _
  | F4 F h => exact CatalogueOrders.F4_card _
  | triality E h => exact CatalogueOrders.triality_card _ _ E.finrank
  | suzuki F m hm hc => exact CatalogueOrders.suzuki_card _ m hc
  | smallRee F m hm hc => exact CatalogueOrders.smallRee_card _ m hc
  | fixed x => exact x.card

/-- Direct non-isomorphism of the actual models whenever the arithmetic labels
are outside the explicitly classified order-collision relation. -/
theorem not_isomorphic_of_not_collision (x y : Entry)
    (h : ¬ Collision (label x) (label y)) : ¬ Nonempty (Model x ≃* Model y) := by
  apply Atlas.Comparisons.not_isomorphic_of_card_ne
  rw [card, card]
  exact catalogue_order_ne (admissible x) (admissible y) h

end Atlas.Comparisons.Catalogue
