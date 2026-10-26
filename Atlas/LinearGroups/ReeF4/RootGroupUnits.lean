import Atlas.LinearGroups.ReeF4.TorusFieldWeights

noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The scalar parametrization needed to obtain every central root parameter
as the square parameter of an actual short-root element. -/
def thetaNormEquiv {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) : Fˣ ≃* Fˣ where
  toFun a := a * thetaUnits m a
  invFun a := thetaUnits m a * a⁻¹
  left_inv a := by
    simp only [map_mul, thetaUnits_square hcard, mul_inv_rev, pow_two]
    simp [mul_assoc, mul_comm, mul_left_comm]
  right_inv a := by
    simp only [map_mul, map_inv, thetaUnits_square hcard, pow_two]
    simp [mul_assoc, mul_comm, mul_left_comm]
  map_mul' a b := by
    simp only [map_mul]
    ac_rfl

end Atlas.ReeF4
