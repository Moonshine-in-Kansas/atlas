import Atlas.Algebra.Albert.PolynomialStabilizer

noncomputable section
namespace Atlas.F4
variable (F : Type*) [Field F]

/-- Full linear stabilizer of the actual split Albert cubic polynomial and unit. -/
abbrev Model := Atlas.Albert.polynomialStabilizer (F := F)

def representation : Model F →* (Atlas.Albert.Carrier F ≃ₗ[F] Atlas.Albert.Carrier F) :=
  (Atlas.Albert.polynomialStabilizer (F := F)).subtype

theorem representation_injective : Function.Injective (representation F) := Subtype.val_injective

instance [Finite F] : Finite (Model F) :=
  Finite.of_injective (fun g : Model F => (g.val : Atlas.Albert.Carrier F →
    Atlas.Albert.Carrier F)) (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

theorem finite_model [Finite F] : Finite (Model F) := inferInstance

end Atlas.F4
