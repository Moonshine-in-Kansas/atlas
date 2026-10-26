import Atlas.Comparisons.CatalogueModels
import Atlas.OrderArithmetic.Normalization

/-! Trusted reference specification for the actual-group comparison interface.
The two deliberate proof holes below are specification-only. This file is never
imported by the solution or by an ATLAS mathematical module. The concrete model,
parameter and normalization definitions in the two imports are part of the
reviewed reference boundary; this is not a mathlib-only existence contract. -/

open Atlas.Comparisons.Catalogue

theorem AtlasComparison.main (x y : Entry) :
    Nonempty (Model x ≃* Model y) ↔
      Atlas.OrderArithmetic.normalize (label x) =
        Atlas.OrderArithmetic.normalize (label y) := by
  sorry

theorem AtlasComparison.nonisomorphic (x y : Entry)
    (h : Atlas.OrderArithmetic.normalize (label x) ≠
      Atlas.OrderArithmetic.normalize (label y)) :
    ¬ Nonempty (Model x ≃* Model y) := by
  sorry
