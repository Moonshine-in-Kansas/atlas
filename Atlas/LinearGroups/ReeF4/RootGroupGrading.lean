import Atlas.LinearGroups.ReeF4.TorusFieldWeights

/-! The two integral degrees controlling conjugation of the source short-root
operator by the norm-parameter torus. These degrees are not field exponents
modulo a guessed group order. -/
namespace Atlas.ReeF4

def shortRootGrade (r : ShortRootLabel) : ℤ × ℤ :=
  ((torusConstantExponents r).1 + 2*(torusThetaExponents r).1,
   (torusConstantExponents r).1 + (torusThetaExponents r).1)

variable {G : Type*} [CommGroup G]

def shortRootGradingWeight (u v : G) (r : ShortRootLabel) : G :=
  u ^ (shortRootGrade r).1 * v ^ (shortRootGrade r).2

theorem twistedTorusWeight_norm (τ : G →* G) (u : G) (hu : τ (τ u) = u^2)
    (r : ShortRootLabel) :
    twistedTorusWeight τ (u*τ u) 1 r = shortRootGradingWeight u (τ u) r := by
  simp only [twistedTorusWeight, torusCharacter, map_mul, map_one, one_zpow, mul_one,
    hu, pow_two, shortRootGradingWeight, shortRootGrade, two_mul, zpow_add, mul_zpow]
  ac_rfl

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem torusWeight_normParameter {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (u : Fˣ) (r : ShortRootLabel) :
    torusWeight m (u*thetaUnits m u) 1 r = shortRootGradingWeight u (thetaUnits m u) r := by
  rw [torusWeight_eq_twisted m (thetaUnits m) (u*thetaUnits m u) 1
    (thetaUnits_apply m _) (thetaUnits_apply m _)]
  exact twistedTorusWeight_norm (thetaUnits m) u (thetaUnits_square hcard u) r

end Atlas.ReeF4
