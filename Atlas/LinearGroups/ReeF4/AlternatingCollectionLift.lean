import Atlas.LinearGroups.ReeF4.AlternatingRootWordCoordinates

namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Abstract action expansion, without unfolding any concrete root operator. -/
theorem modelProduct_apply (m : ℕ) (g h : Model F m) (w : TraceZero F) :
    (g*h).val w = g.val (h.val w) := rfl

theorem model_ext_of_carrier_action {m : ℕ} (g h : Model F m)
    (he : ∀ w : TraceZero F, (g.val w).val = (h.val w).val) : g = h := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  exact Subtype.ext (he w)

/- For each compiled Carrier formula identity, lift by:
  apply model_ext_of_carrier_action
  intro w
  simp only [modelProduct_apply, alternatingShortFactor_pair_val,
    alternatingLongFactor_val]
  exact alternatingCollection_ji_formula hcard ... w.val

The existing public bridges are:
* alternatingShortFactor_val hcard k a b w
* alternatingShortFactor_pair_val hcard k v w
* alternatingLongFactor_val hcard k u w
They expose precisely the formulas used by the collection leaves.
The pre-existing model_mul_apply in AlternatingRootWordCoordinates is private;
the tiny public helper above avoids depending on a mangled private name.
-/
end Atlas.ReeF4
