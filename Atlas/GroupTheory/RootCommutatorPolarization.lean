import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-! Polarization of an actual quadratic commutator formula. The cancellation
is in the target group, never by the coefficient 2 in the ring. -/
namespace Atlas.GroupTheory
open scoped commutatorElement
variable {R G : Type*} [CommRing R] [Group G]

/-- A quadratic mixed commutator determines the short--short commutator,
including when 2 is zero or a zero divisor. All required centralizing
relations are explicit. -/
theorem root_commutator_polarization
    (x z w : Multiplicative R →* G) (y : G)
    (hcomm : ∀ s : R, ⁅x (Multiplicative.ofAdd s), y⁆ =
      z (Multiplicative.ofAdd (-s)) * w (Multiplicative.ofAdd (s ^ 2)))
    (hxw : ∀ s t : R, Commute (x (Multiplicative.ofAdd s))
      (w (Multiplicative.ofAdd t)))
    (hzw : ∀ s t : R, Commute (z (Multiplicative.ofAdd s))
      (w (Multiplicative.ofAdd t)))
    (s t : R) :
    ⁅x (Multiplicative.ofAdd s), z (Multiplicative.ofAdd t)⁆ =
      w (Multiplicative.ofAdd (-2 * s * t)) := by
  let X : R → G := fun a => x (Multiplicative.ofAdd a)
  let Z : R → G := fun a => z (Multiplicative.ofAdd a)
  let W : R → G := fun a => w (Multiplicative.ofAdd a)
  have hx_add (a b : R) : X (a + b) = X a * X b := x.map_mul _ _
  have hz_add (a b : R) : Z (a + b) = Z a * Z b := z.map_mul _ _
  have hw_add (a b : R) : W (a + b) = W a * W b := w.map_mul _ _
  have hc (a : R) : ⁅X a, y⁆ = Z (-a) * W (a ^ 2) := hcomm a
  have hconj (a b : R) :
      X a * (Z (-b) * W (b ^ 2)) * (X a)⁻¹ =
        (X a * Z (-b) * (X a)⁻¹) * W (b ^ 2) := by
    have hfix : X a * W (b ^ 2) * (X a)⁻¹ = W (b ^ 2) := by
      rw [(hxw a (b ^ 2)).eq]
      simp only [X, W, mul_assoc, mul_inv_cancel, mul_one]
    calc
      _ = (X a * Z (-b) * (X a)⁻¹) *
          (X a * W (b ^ 2) * (X a)⁻¹) := by group
      _ = _ := by rw [hfix]
  have hpolar (a b : R) : ⁅X a, Z (-b)⁆ = W (2 * a * b) := by
    have hsum : Z (-(a + b)) * W ((a + b) ^ 2) =
        X a * (Z (-b) * W (b ^ 2)) * (X a)⁻¹ *
          (Z (-a) * W (a ^ 2)) := by
      have h := commutatorElement_mul_left_eq_conj_mul (X a) (X b) y
      rw [← hx_add a b, hc (a + b), hc b, hc a] at h
      exact h
    have htail : Z (-b) * W (b ^ 2) * Z (-a) * W (a ^ 2) =
        Z (-(a + b)) * W (b ^ 2 + a ^ 2) := by
      calc
        _ = (Z (-b) * Z (-a)) * (W (b ^ 2) * W (a ^ 2)) := by
          simpa only [mul_assoc] using
            (hzw (-a) (b ^ 2)).symm.mul_mul_mul_comm (Z (-b)) (W (a ^ 2))
        _ = Z (-b + -a) * W (b ^ 2 + a ^ 2) := by rw [← hz_add, ← hw_add]
        _ = _ := by rw [show -b + -a = -(a + b) by ring]
    have hleft :
        ⁅X a, Z (-b)⁆ * (Z (-b) * W (b ^ 2) * Z (-a) * W (a ^ 2)) =
          Z (-(a + b)) * W ((a + b) ^ 2) := by
      calc
        _ = X a * (Z (-b) * W (b ^ 2)) * (X a)⁻¹ *
            (Z (-a) * W (a ^ 2)) := by
          rw [hconj]
          simp only [commutatorElement_def]
          group
        _ = _ := hsum.symm
    have hright :
        W (2 * a * b) * (Z (-b) * W (b ^ 2) * Z (-a) * W (a ^ 2)) =
          Z (-(a + b)) * W ((a + b) ^ 2) := by
      rw [htail]
      calc
        _ = Z (-(a + b)) * (W (2 * a * b) * W (b ^ 2 + a ^ 2)) :=
          (hzw (-(a + b)) (2 * a * b)).symm.left_comm _
        _ = Z (-(a + b)) * W (2 * a * b + (b ^ 2 + a ^ 2)) := by
          rw [← hw_add]
        _ = _ := by rw [show 2 * a * b + (b ^ 2 + a ^ 2) = (a + b) ^ 2 by ring]
    exact mul_right_cancel (hleft.trans hright.symm)
  simpa only [X, Z, W, neg_neg, mul_neg, neg_mul] using hpolar s (-t)

end Atlas.GroupTheory
