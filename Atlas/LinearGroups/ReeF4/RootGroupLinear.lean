import Atlas.LinearGroups.ReeF4.RootGroupRelations

/-! Bundled linear laws of the two-parameter short-root operators. -/
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem shortRootParameterLinear_zero (τ : F →+* F) :
    shortRootParameterLinear τ 0 = LinearMap.id := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  exact shortRootParameterFormula_zero τ w.val

theorem shortRootCenterLinear_zero (τ : F →+* F) :
    shortRootCenterLinear τ 0 = LinearMap.id := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  exact shortRootCenterFormula_zero τ w.val

theorem shortRootCenterLinear_add (τ : F →+* F) (a b : F) :
    (shortRootCenterLinear τ a).comp (shortRootCenterLinear τ b) =
      shortRootCenterLinear τ (a+b) := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  simpa only [LinearMap.comp_apply, shortRootCenterLinear_val] using
    shortRootCenterFormula_add τ a b w.val

theorem shortRootParameterLinear_center_comm (τ : F →+* F) (a b : F) :
    (shortRootParameterLinear τ a).comp (shortRootCenterLinear τ b) =
      (shortRootCenterLinear τ b).comp (shortRootParameterLinear τ a) := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  simpa only [LinearMap.comp_apply, shortRootParameterLinear_val, shortRootCenterLinear_val] using
    shortRootParameterFormula_center_comm τ a b w.val

theorem shortRootParameterLinear_mul (τ : F →+* F) (a b : F) (ha : τ (τ a) = a^2) :
    (shortRootParameterLinear τ a).comp (shortRootParameterLinear τ b) =
      (shortRootParameterLinear τ (a+b)).comp (shortRootCenterLinear τ (τ a*b)) := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  simpa only [LinearMap.comp_apply, shortRootParameterLinear_val, shortRootCenterLinear_val] using
    shortRootParameterFormula_mul τ a b ha w.val

def shortRootPairLinear (τ : F →+* F) (a b : F) : Module.End F (TraceZero F) :=
  shortRootParameterLinear τ a * shortRootCenterLinear τ b

theorem shortRootPairLinear_zero (τ : F →+* F) : shortRootPairLinear τ 0 0 = 1 := by
  simp only [shortRootPairLinear, shortRootParameterLinear_zero, shortRootCenterLinear_zero]
  rfl

theorem shortRootPairLinear_mul (τ : F →+* F) (a b c d : F) (ha : τ (τ a) = a^2) :
    shortRootPairLinear τ a b * shortRootPairLinear τ c d =
      shortRootPairLinear τ (a+c) (b+d+τ a*c) := by
  let X := shortRootParameterLinear τ
  let Y := shortRootCenterLinear τ
  have hc : Y b * X c = X c * Y b := (shortRootParameterLinear_center_comm τ c b).symm
  have hx : X a * X c = X (a+c) * Y (τ a*c) := shortRootParameterLinear_mul τ a c ha
  have hy (u v : F) : Y u * Y v = Y (u+v) := shortRootCenterLinear_add τ u v
  change (X a * Y b) * (X c * Y d) = X (a+c) * Y (b+d+τ a*c)
  calc
    _ = (X a * X c) * (Y b * Y d) := by
      simp only [mul_assoc]
      rw [← mul_assoc (Y b) (X c) (Y d), hc, mul_assoc]
    _ = X (a+c) * Y (τ a*c+(b+d)) := by rw [hx, hy, mul_assoc, hy]
    _ = _ := by rw [add_comm (τ a*c) (b+d)]

theorem shortRootPairLinear_inverse (τ : F →+* F) (a b : F) (ha : τ (τ a) = a^2) :
    shortRootPairLinear τ a b * shortRootPairLinear τ a (b+a*τ a) = 1 := by
  rw [shortRootPairLinear_mul τ a b a (b+a*τ a) ha]
  have h : b+(b+a*τ a)+τ a*a = 0 := by
    linear_combination (b+a*τ a) * (CharTwo.two_eq_zero (R := F))
  rw [CharTwo.add_self_eq_zero, h, shortRootPairLinear_zero]

theorem shortRootPairLinear_inverse_left (τ : F →+* F) (a b : F) (ha : τ (τ a) = a^2) :
    shortRootPairLinear τ a (b+a*τ a) * shortRootPairLinear τ a b = 1 := by
  rw [shortRootPairLinear_mul τ a (b+a*τ a) a b ha]
  have h : (b+a*τ a)+b+τ a*a = 0 := by
    linear_combination (b+a*τ a) * (CharTwo.two_eq_zero (R := F))
  rw [CharTwo.add_self_eq_zero, h, shortRootPairLinear_zero]

end Atlas.ReeF4
