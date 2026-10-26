import Atlas.LinearGroups.SuzukiFamily.Twist

/-! The inverse Tits convention for the large Ree partial product.
The inverse identities use the finite-field cardinality; they are not free
polynomial identities. No group order or simplicity result is imported. -/
noncomputable section
namespace Atlas.ReeF4
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

abbrev theta (m : ℕ) : F ≃+* F := SuzukiFamily.theta F m

def thetaInv (m : ℕ) : F ≃+* F := iterateFrobeniusEquiv F 2 m

@[simp] theorem thetaInv_apply (m : ℕ) (x : F) :
    thetaInv F m x = x ^ (2 ^ m) := rfl

variable {F} {m : ℕ}
theorem thetaInv_theta (hcard : Nat.card F = 2^(2*m+1)) (x : F) :
    thetaInv F m (theta F m x) = x := by
  change iterateFrobeniusEquiv F 2 m (iterateFrobeniusEquiv F 2 (m+1) x) = x
  rw [← iterateFrobeniusEquiv_add_apply]
  rw [show m + (m+1) = 2*m+1 by omega]
  exact SuzukiFamily.frobenius_period hcard x

theorem theta_thetaInv (hcard : Nat.card F = 2^(2*m+1)) (x : F) :
    theta F m (thetaInv F m x) = x := by
  change iterateFrobeniusEquiv F 2 (m+1) (iterateFrobeniusEquiv F 2 m x) = x
  rw [← iterateFrobeniusEquiv_add_apply]
  rw [show m+1+m = 2*m+1 by omega]
  exact SuzukiFamily.frobenius_period hcard x

theorem thetaInv_eq_symm (hcard : Nat.card F = 2^(2*m+1)) :
    thetaInv F m = (theta F m).symm := by
  ext x
  apply (theta F m).injective
  simp only [theta_thetaInv hcard, RingEquiv.apply_symm_apply]

theorem thetaInv_sq (m : ℕ) (x : F) :
    thetaInv F m (x^2) = theta F m x := by
  change (x^2)^(2^m) = x^(2^(m+1))
  rw [← pow_mul, pow_succ, Nat.mul_comm 2]

theorem thetaInv_apply_sq (m : ℕ) (x : F) :
    (thetaInv F m x)^2 = theta F m x := by
  rw [← map_pow, thetaInv_sq]

theorem thetaInv_square_sq (hcard : Nat.card F = 2^(2*m+1)) (x : F) :
    thetaInv F m (thetaInv F m (x^2)) = x := by
  rw [thetaInv_sq, thetaInv_theta hcard]

theorem thetaInv_binary (x : F) : thetaInv F 0 x = x := by simp

variable {K : Type*} [Field K] [Finite K] [CharP K 2]
theorem map_thetaInv (e : F ≃+* K) (m : ℕ) (x : F) :
    e (thetaInv F m x) = thetaInv K m (e x) := by
  simp only [thetaInv_apply, map_pow]
end Atlas.ReeF4
