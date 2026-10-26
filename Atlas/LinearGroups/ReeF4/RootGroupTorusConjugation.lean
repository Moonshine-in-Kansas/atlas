import Atlas.LinearGroups.ReeF4.RootGroupConjugation
import Atlas.LinearGroups.ReeF4.RootGroupEquiv
import Atlas.LinearGroups.ReeF4.ShortRootOrder
import Atlas.LinearGroups.ReeF4.TorusGroup

/-! Identification of the polynomial root parametrization with actual torus
conjugation of Wilson's previously checked order-four operator. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem torusWeight_inverseNormParameter {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u : Fˣ) (r : ShortRootLabel) :
    torusWeight m (u*thetaUnits m u)⁻¹ 1 r =
      (shortRootGradingWeight u (thetaUnits m u) r)⁻¹ := by
  have hi : torusWeight m (u*thetaUnits m u)⁻¹ 1 r =
      (torusWeight m (u*thetaUnits m u) 1 r)⁻¹ := by
    simp only [torusWeight, one_zpow, mul_one]
    exact inv_zpow _ _
  rw [hi, torusWeight_normParameter hcard]

theorem shortRootParameterLinear_torusConjugate {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u : Fˣ) :
    shortRootParameterLinear (theta F m).toRingHom (u : F) =
      (torusEquiv m (u*thetaUnits m u)⁻¹ 1).toLinearMap.comp
        (shortRootLinear.comp (torusEquiv m (u*thetaUnits m u) 1).toLinearMap) := by
  apply LinearMap.ext
  intro w
  rw [← shortRootCoordinateLinear_eq]
  apply Subtype.ext
  change shortRootParameterFormula (theta F m).toRingHom (u : F) w.val =
    rootDiagonalFormula (torusWeight m (u*thetaUnits m u)⁻¹ 1)
      (shortRootFormula (rootDiagonalFormula (torusWeight m (u*thetaUnits m u) 1) w.val))
  have h1 : torusWeight m (u*thetaUnits m u) 1 =
      shortRootGradingWeight u (thetaUnits m u) := by
    funext r
    exact torusWeight_normParameter hcard u r
  have h2 : torusWeight m (u*thetaUnits m u)⁻¹ 1 =
      fun r => (shortRootGradingWeight u (thetaUnits m u) r)⁻¹ := by
    funext r
    exact torusWeight_inverseNormParameter hcard u r
  rw [h1, h2]
  exact (shortRootGraded_conjugation (theta F m).toRingHom u w.val).symm

theorem shortRootPairEquiv_unit_zero {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u : Fˣ) :
    shortRootPairEquiv m hcard (u : F) 0 =
      torusEquiv m (u*thetaUnits m u)⁻¹ 1 * shortRootEquiv *
        torusEquiv m (u*thetaUnits m u) 1 := by
  apply LinearEquiv.toLinearMap_injective
  change shortRootParameterLinear (theta F m).toRingHom (u : F) *
      shortRootCenterLinear (theta F m).toRingHom 0 =
    ((torusEquiv m (u*thetaUnits m u)⁻¹ 1).toLinearMap * shortRootLinear) *
      (torusEquiv m (u*thetaUnits m u) 1).toLinearMap
  rw [shortRootCenterLinear_zero]
  change shortRootParameterLinear (theta F m).toRingHom (u : F) * 1 =
    ((torusEquiv m (u*thetaUnits m u)⁻¹ 1).toLinearMap * shortRootLinear) *
      (torusEquiv m (u*thetaUnits m u) 1).toLinearMap
  rw [mul_one, mul_assoc]
  exact shortRootParameterLinear_torusConjugate hcard u

end Atlas.ReeF4
