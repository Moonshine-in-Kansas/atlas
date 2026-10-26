import Atlas.LinearGroups.ReeF4.IntrinsicGroup

/-! Finiteness of the literal full stabilizer, independent of its order. -/
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

instance modelFinite (m : ℕ) : Finite (Model F m) := by
  letI : Finite (TraceZero F) := Finite.of_injective
    (traceZeroCoordinateEquiv (F := F)) (traceZeroCoordinateEquiv (F := F)).injective
  exact Finite.of_injective (fun g : Model F m => fun w : TraceZero F => g.val w) (by
    intro g h he
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    exact congrFun he w)

end Atlas.ReeF4
