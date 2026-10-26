import Atlas.Comparisons.Exceptional.E6.MatrixReduction
import Atlas.Comparisons.Exceptional.E6.ReductionKernels

/-! Actual integral Weyl reduction acts on the five-dimensional ternary quotient. -/
noncomputable section
namespace Atlas.Comparisons.E6Lattice
open Matrix

def ternaryMatrix : IntegralWeyl →* GeneralLinearGroup (Fin 6) (ZMod 3) :=
  (GeneralLinearGroup.map (Int.castRingHom (ZMod 3))).comp integralMatrix

def ternaryLinear : IntegralWeyl →* ((Fin 6 → ZMod 3) ≃ₗ[ZMod 3] (Fin 6 → ZMod 3)) :=
  (GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Fin 6 → ZMod 3))).toMonoidHom.comp
      ternaryMatrix

theorem ternaryLinear_action (g : IntegralWeyl) (x : Fin 6 → ℤ) :
    ternaryLinear g (reduceTernary x) = reduceTernary (g.val.val x) := by
  change (integralMatrix g).val.map (Int.castRingHom (ZMod 3)) *ᵥ
    (fun i => (x i : ZMod 3)) = _
  rw [integralMatrix_val]
  funext i
  exact ((Int.castRingHom (ZMod 3)).map_mulVec
    (LinearMap.toMatrix' g.val.val.toLinearMap) x i).symm.trans (by
      rw [LinearMap.toMatrix'_mulVec]
      rfl)

theorem ternaryLinear_radical (g : IntegralWeyl) (a : ZMod 3) :
    ternaryLinear g (radicalVector a) = radicalVector a := by
  have hr : radicalVector a = a • reduceTernary dualNumerator := by
    revert a
    decide
  rw [hr,map_smul,ternaryLinear_action]
  have hg := weyl_le_discriminantFixer g.prop
  change reduceTernary (g.val.val dualNumerator) = reduceTernary dualNumerator at hg
  rw [hg]

theorem quotient_section_difference (x : Fin 6 → ZMod 3) :
    quotientSection (quotientCoordinates x) = x - radicalVector (x 0) := by
  funext i
  fin_cases i <;> simp [quotientSection,quotientCoordinates,radicalVector]

@[simp] theorem quotient_radical (a : ZMod 3) : quotientCoordinates (radicalVector a) = 0 := by
  funext i
  fin_cases i <;> simp [quotientCoordinates,radicalVector]

def ternaryQuotientMap (g : IntegralWeyl) : (Fin 5 → ZMod 3) →ₗ[ZMod 3] (Fin 5 → ZMod 3) :=
  quotientProjectionLinear.comp ((ternaryLinear g).toLinearMap.comp quotientSectionLinear)

theorem ternaryQuotient_intertwines (g : IntegralWeyl) (x : Fin 6 → ZMod 3) :
    ternaryQuotientMap g (quotientCoordinates x) = quotientCoordinates (ternaryLinear g x) := by
  change quotientProjectionLinear (ternaryLinear g (quotientSection (quotientCoordinates x))) = _
  rw [quotient_section_difference,map_sub,ternaryLinear_radical,map_sub]
  change quotientCoordinates (ternaryLinear g x) - quotientCoordinates (radicalVector (x 0)) = _
  rw [quotient_radical,sub_zero]

theorem ternaryQuotientMap_mul (g h : IntegralWeyl) :
    ternaryQuotientMap (g*h) = (ternaryQuotientMap g).comp (ternaryQuotientMap h) := by
  apply LinearMap.ext
  intro x
  change quotientCoordinates (ternaryLinear (g*h) (quotientSection x)) =
    ternaryQuotientMap g (quotientCoordinates (ternaryLinear h (quotientSection x)))
  rw [ternaryQuotient_intertwines,map_mul]
  rfl

theorem ternaryQuotientMap_one : ternaryQuotientMap 1 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change quotientCoordinates (ternaryLinear 1 (quotientSection x)) = x
  rw [map_one]
  exact quotient_section x

def ternaryQuotientLinear (g : IntegralWeyl) :
    (Fin 5 → ZMod 3) ≃ₗ[ZMod 3] (Fin 5 → ZMod 3) :=
  LinearEquiv.ofLinearMap (ternaryQuotientMap g) (ternaryQuotientMap g⁻¹)
    (by rw [← ternaryQuotientMap_mul,mul_inv_cancel,ternaryQuotientMap_one])
    (by rw [← ternaryQuotientMap_mul,inv_mul_cancel,ternaryQuotientMap_one])

def ternaryQuotientRepresentation : IntegralWeyl →*
    ((Fin 5 → ZMod 3) ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) where
  toFun := ternaryQuotientLinear
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    exact ternaryQuotientMap_one
  map_mul' g h := by
    apply LinearEquiv.toLinearMap_injective
    exact ternaryQuotientMap_mul g h

end Atlas.Comparisons.E6Lattice
