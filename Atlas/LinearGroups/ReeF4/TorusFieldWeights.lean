import Atlas.LinearGroups.ReeF4.TorusTwistedWeights
import Atlas.LinearGroups.ReeF4.Twist

/-! The torus/star weight law over the actual admissible finite fields. This
uses the verified Frobenius twist; no identity in free parameter polynomials
is asserted. -/
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def thetaUnits (m : ℕ) : Fˣ →* Fˣ := Units.map (theta F m).toMonoidHom

theorem thetaUnits_apply (m : ℕ) (a : Fˣ) :
    thetaUnits m a = a ^ (2^(m+1)) := by
  apply Units.ext
  rfl

theorem thetaUnits_square {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (a : Fˣ) :
    thetaUnits m (thetaUnits m a) = a^2 := by
  apply Units.ext
  exact SuzukiFamily.theta_square hcard (a : F)

theorem torusWeight_star_theta {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (a b : Fˣ) (r s : ShortRootLabel)
    (hp : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0) :
    torusWeight (G := Fˣ) m a b r * torusWeight (G := Fˣ) m a b s =
      thetaUnits m (torusWeight (G := Fˣ) m a b (starRootTarget r s)) := by
  simp only [torusWeight_eq_twisted m (thetaUnits m) a b
    (thetaUnits_apply m a) (thetaUnits_apply m b)]
  exact twistedTorusWeight_star (thetaUnits m) a b
    (thetaUnits_square hcard a) (thetaUnits_square hcard b) r s hp

theorem torusWeight_star_thetaInv {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (a b : Fˣ) (r s : ShortRootLabel)
    (hp : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0) :
    thetaInv F m ((torusWeight (G := Fˣ) m a b r : F) * (torusWeight (G := Fˣ) m a b s : F)) =
      (torusWeight (G := Fˣ) m a b (starRootTarget r s) : F) := by
  have h := congrArg (fun u : Fˣ => (u : F)) (torusWeight_star_theta hcard a b r s hp)
  change (torusWeight (G := Fˣ) m a b r : F) * (torusWeight (G := Fˣ) m a b s : F) =
    theta F m (torusWeight (G := Fˣ) m a b (starRootTarget r s) : F) at h
  rw [h, thetaInv_theta hcard]

end Atlas.ReeF4
