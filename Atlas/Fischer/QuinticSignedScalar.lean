import Atlas.Fischer.QuinticThetaExponent
import Atlas.Fischer.SignedMonomialGeometry

namespace Atlas.Fischer

theorem parkerScalarSign_natCast (n : ℕ) :
    parkerScalarSign (n : ParkerBit) = (-1 : Scalar)^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.cast_add, parkerScalarSign_add, ih, pow_succ]
    rfl

/-- The sign and theta calculation is independent of the octad counting.
Its only hypotheses are the derived binary parity and six-sign identities. -/
theorem quintic_signed_scalar (e d0 d1 d2 d3 d4 s : ℕ)
    (be b0 b1 b2 b3 b4 : ParkerBit)
    (he : e ≤ 1) (h0 : d0 ≤ 1) (h1 : d1 ≤ 1) (h2 : d2 ≤ 1)
    (h3 : d3 ≤ 1) (h4 : d4 ≤ 1)
    (hp : (d0+d1+d2+d3+d4)%2=e)
    (hs : be+b0+b1+b2+b4+b3=(s : ParkerBit)) :
    16 * ((theta^d0 / 2 * parkerScalarSign b0) *
      (theta^d4 / 2 * parkerScalarSign b4) *
      star (theta^d1 / 2 * parkerScalarSign b1) *
      star (theta^d2 / 2 * parkerScalarSign b2) *
      star (theta^d3 / 2 * parkerScalarSign b3)) =
      star (theta^e / 2 * parkerScalarSign be) *
        (-1 : Scalar)^(s+d0+d4) * (-3 : Scalar)^((d0+d1+d2+d3+d4-e)/2) := by
  have hsign := congrArg parkerScalarSign hs
  simp only [parkerScalarSign_add, parkerScalarSign_natCast] at hsign
  have hfive : parkerScalarSign b0 * parkerScalarSign b4 * parkerScalarSign b1 *
      parkerScalarSign b2 * parkerScalarSign b3 = parkerScalarSign be * (-1 : Scalar)^s := by
    calc
      _ = (parkerScalarSign be * parkerScalarSign be) *
          (parkerScalarSign b0 * parkerScalarSign b4 * parkerScalarSign b1 *
            parkerScalarSign b2 * parkerScalarSign b3) := by rw [parkerScalarSign_square, one_mul]
      _ = parkerScalarSign be * (parkerScalarSign be * parkerScalarSign b0 *
          parkerScalarSign b1 * parkerScalarSign b2 * parkerScalarSign b4 *
          parkerScalarSign b3) := by ring
      _ = _ := by rw [hsign]
  have ht := quintic_theta_exponent e d0 d1 d2 d3 d4 he h0 h1 h2 h3 h4 hp
  simp only [star_mul, star_div₀, star_ofNat, parkerScalarSign_star]
  rw [Nat.add_assoc s d0 d4, pow_add]
  linear_combination hfive * (theta^d0 * theta^d4 * star (theta^d1) *
      star (theta^d2) * star (theta^d3)) / 2 +
    ht * (parkerScalarSign be * (-1 : Scalar)^s) / 2

end Atlas.Fischer
