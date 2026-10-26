import Atlas.Comparisons

/-! Solutions of the explicit actual-group comparison contracts.
The reference specification is intentionally not imported. -/

open Atlas.Comparisons.Catalogue

theorem AtlasComparison.main (x y : Entry) :
    Nonempty (Model x ≃* Model y) ↔
      Atlas.OrderArithmetic.normalize (label x) =
        Atlas.OrderArithmetic.normalize (label y) :=
  isomorphic_iff_normalized_label_eq x y

theorem AtlasComparison.nonisomorphic (x y : Entry)
    (h : Atlas.OrderArithmetic.normalize (label x) ≠
      Atlas.OrderArithmetic.normalize (label y)) :
    ¬ Nonempty (Model x ≃* Model y) :=
  not_isomorphic_of_normalized_label_ne x y h
