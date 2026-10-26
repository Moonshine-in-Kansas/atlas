import Atlas.Sporadic.Janko1.Generators

/-! Exact actions of the prescribed four automorphisms on the cyclic basis. -/
namespace Atlas.Janko1

def linearRepresentation : G2.Model Field →* Module.End Field (SplitOctonion.Carrier Field) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (G2.representation Field)

theorem linearRepresentation_injective : Function.Injective linearRepresentation := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact he

theorem generator_pow (g : Fin 4) : generator g ^ generatorExponent g = 1 := by
  apply linearRepresentation_injective
  rw [map_pow, map_one]
  exact generatorLinear_pow g

theorem P_pow : P^7 = 1 := generator_pow 0
theorem Q_pow : Q^3 = 1 := generator_pow 1
theorem R_pow : R^2 = 1 := generator_pow 2
theorem S_pow : S^2 = 1 := generator_pow 3

set_option maxRecDepth 8192 in
theorem P_imaginary : ∀ t : Fin 7,
    P.val (imaginaryVector t) = imaginaryVector (t+1) := by decide

set_option maxRecDepth 8192 in
theorem Q_imaginary : ∀ t : Fin 7,
    Q.val (imaginaryVector t) = imaginaryVector (2*t) := by decide

set_option maxRecDepth 8192 in
theorem R_imaginary : ∀ t : Fin 7,
    R.val (imaginaryVector t) =
      (if t = 0 ∨ t = 3 ∨ t = 5 ∨ t = 6 then (-1 : Field) else 1) • imaginaryVector t := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
-- Seven short coordinate equalities in the installed octonion algebra.
theorem S_imaginary : ∀ t : Fin 7,
    S.val (imaginaryVector t) =
      (-2 : Field) • imaginaryVector (-t) +
      (imaginaryVector (1-t) + imaginaryVector (2-t) + imaginaryVector (4-t)) +
      (3 : Field) • (imaginaryVector (6-t) + imaginaryVector (5-t) + imaginaryVector (3-t)) := by
  decide

theorem finite_model : Finite Model := inferInstance

end Atlas.Janko1
