import Atlas.Algebra.SplitOctonion.Automorphism
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The actual full split-octonion automorphism model; no order or simplicity assumptions. -/
namespace Atlas.G2
variable (F : Type*) [Field F]

abbrev Model := Atlas.SplitOctonion.Automorphism F

instance [Finite F] : Finite (Model F) :=
  Finite.of_injective (fun g : Model F => (g.val : Atlas.SplitOctonion.Carrier F →
    Atlas.SplitOctonion.Carrier F)) (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

/-- The defining eight-dimensional faithful linear representation. -/
def representation : Model F →* (Atlas.SplitOctonion.Carrier F ≃ₗ[F]
    Atlas.SplitOctonion.Carrier F) :=
  Atlas.Algebra.MultiplicativeLinearAut.representation

theorem representation_injective : Function.Injective (representation F) :=
  Atlas.Algebra.MultiplicativeLinearAut.representation_injective

theorem carrier_finrank : Module.finrank F (Atlas.SplitOctonion.Carrier F) = 8 := by
  simp [Atlas.SplitOctonion.Carrier]
theorem finite_model [Finite F] : Finite (Model F) := inferInstance
end Atlas.G2
