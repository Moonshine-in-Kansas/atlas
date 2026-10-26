import Atlas.Comparisons.Exceptional.E6.TernaryOrthogonal
import Atlas.Comparisons.Exceptional.E6.IntegralDeterminant

/-! A concrete determinant-one word has nonidentity ternary quotient action. -/
noncomputable section
namespace Atlas.Comparisons.E6Lattice

def ternaryWitness : positiveWeyl :=
  ⟨⟨simpleReflection ℤ 0,simpleReflection_mem ℤ 0⟩ *
    ⟨simpleReflection ℤ 1,simpleReflection_mem ℤ 1⟩, by
    change integralDeterminant (_ * _) = 1
    rw [map_mul,simpleReflection_integralDeterminant,simpleReflection_integralDeterminant]
    simp⟩

theorem ternaryWitness_action :
    (ternaryQuotientRepresentation ternaryWitness.val ![1,0,0,0,0]) 2 = 1 := by
  change (quotientCoordinates (ternaryLinear ternaryWitness.val
    (quotientSection ![1,0,0,0,0]))) 2 = 1
  have hvec : quotientSection (![1,0,0,0,0] : Fin 5 → ZMod 3) =
      reduceTernary (simpleRoot 1) := by decide
  rw [hvec,ternaryLinear_action]
  change (quotientCoordinates (reduceTernary
    (reflection 0 (reflection 1 (simpleRoot 1))))) 2 = 1
  decide

theorem ternaryWitness_representation_ne_one :
    ternaryQuotientRepresentation ternaryWitness.val ≠ 1 := by
  intro h
  have hv := ternaryWitness_action
  rw [h] at hv
  change (0 : ZMod 3) = 1 at hv
  exact zero_ne_one hv

theorem ternaryWitness_orthogonal_ne_one : intoTernaryB ternaryWitness.val ≠ 1 := by
  intro h
  apply ternaryWitness_representation_ne_one
  have he : intoTernaryQuotient ternaryWitness.val = 1 :=
    ternaryBEquiv.injective (h.trans ternaryBEquiv.map_one.symm)
  exact congrArg Subtype.val he

end Atlas.Comparisons.E6Lattice
