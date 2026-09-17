import Atlas.Fischer.Scalars

namespace Atlas.Fischer

/-- A six-binary-type scalar identity. The parity assumption comes from
Golay triangle closure; no octads or tensor coordinates are enumerated. -/
theorem quintic_theta_exponent (e d0 d1 d2 d3 d4 : ℕ)
    (he : e ≤ 1) (h0 : d0 ≤ 1) (h1 : d1 ≤ 1) (h2 : d2 ≤ 1)
    (h3 : d3 ≤ 1) (h4 : d4 ≤ 1)
    (hp : (d0+d1+d2+d3+d4)%2=e) :
    theta^d0 * theta^d4 * star (theta^d1) * star (theta^d2) * star (theta^d3) =
      star (theta^e) * (-1 : Scalar)^(d0+d4) *
        (-3 : Scalar)^((d0+d1+d2+d3+d4-e)/2) := by
  have ht3 : theta^3 = -3 * theta := by
    rw [show (3 : ℕ) = 2+1 from rfl, pow_succ, theta_sq]
  have ht4 : theta^4 = 9 := by
    calc
      _ = (theta^2)^2 := by ring
      _ = 9 := by rw [theta_sq]; norm_num
  have ht5 : theta^5 = 9 * theta := by
    rw [show (5 : ℕ) = 4+1 from rfl, pow_succ, ht4]
  interval_cases e <;> interval_cases d0 <;> interval_cases d1 <;>
    interval_cases d2 <;> interval_cases d3 <;> interval_cases d4 <;>
    norm_num at hp <;> norm_num [theta_conjugate] <;>
    ring_nf <;> norm_num [theta_sq, ht3, ht4, ht5] <;> ring

end Atlas.Fischer
