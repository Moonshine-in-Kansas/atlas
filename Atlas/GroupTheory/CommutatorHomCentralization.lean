import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic.Group

/-! Cancellation of an additive commutator cocycle. No coefficients are
cancelled in a ring; only multiplication in the target group is cancelled. -/
namespace Atlas.GroupTheory
open scoped commutatorElement

/-- If a commutator splits into two commuting homomorphic factors and the
first is centralized by the input family, so is the second. -/
theorem commute_of_commutator_hom_product
    {A G : Type*} [Monoid A] [Group G]
    (y z w : A →* G) (x : G)
    (hcomm : ∀ a, ⁅x, y a⁆ = z a * w a)
    (hzw : ∀ a b, Commute (z a) (w b))
    (hyz : ∀ a b, Commute (y a) (z b)) (a b : A) :
    Commute (y a) (w b) := by
  have hprod : z (a * b) * w (a * b) = (z a * w a) * (z b * w b) := by
    rw [map_mul, map_mul]
    exact ((hzw b a).symm.mul_mul_mul_comm (z a) (w b)).symm
  have hc := commutatorElement_mul_right_eq_mul_conj x (y a) (y b)
  rw [← y.map_mul, hcomm (a * b), hcomm a, hcomm b, hprod] at hc
  have hfix : z b * w b = y a * (z b * w b) * (y a)⁻¹ := by
    apply mul_left_cancel (a := z a * w a)
    simpa only [mul_assoc] using hc
  have hwhole : Commute (y a) (z b * w b) := by
    change y a * (z b * w b) = (z b * w b) * y a
    calc
      _ = (y a * (z b * w b) * (y a)⁻¹) * y a := by group
      _ = _ := by rw [← hfix]
  change y a * w b = w b * y a
  apply mul_left_cancel (a := z b)
  calc
    z b * (y a * w b) = y a * (z b * w b) := by
      rw [← mul_assoc, (hyz a b).symm.eq, mul_assoc]
    _ = (z b * w b) * y a := hwhole.eq
    _ = z b * (w b * y a) := mul_assoc _ _ _

end Atlas.GroupTheory
