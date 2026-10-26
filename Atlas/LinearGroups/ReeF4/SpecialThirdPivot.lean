import Atlas.LinearGroups.ReeF4.SpecialAdjointTop
import Atlas.LinearGroups.ReeF4.WeylSL2Membership
import Atlas.LinearGroups.ReeF4.WeylModel

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def thirdPivotParameter (m : ℕ) (u : TraceZero F) : F :=
  thetaInv F m (u.val.2 2 5 / u.val.2 2 6)

def thirdPivot {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (u : TraceZero F) : Model F m :=
  ⟨longSL2Equiv (thirdPivotParameter m u) (theta F m (thirdPivotParameter m u)),
    longSL2Parameter_mem_modelSubgroup hcard _⟩

def thirdPivotDescent {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (u : TraceZero F) : Model F m :=
  ⟨weylSigma,weylOperator_mem_modelSubgroup m 1⟩ * thirdPivot hcard u

theorem thirdPivot_C2_zero {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (u : TraceZero F) (hc : u.val.2 2 6 ≠ 0) :
    ((thirdPivot hcard u).val u).val.2 2 5 = 0 := by
  change u.val.2 2 5 + theta F m (thetaInv F m (u.val.2 2 5/u.val.2 2 6))*
    u.val.2 2 6 = 0
  rw [theta_thetaInv hcard,div_mul_cancel₀ _ hc,CharTwo.add_self_eq_zero]

/-- At a C3-leading special vector, zero adjoint forces B2=0. -/
theorem IsSpecialVector.B2_zero_of_leading_C3 {m : ℕ} {u : TraceZero F}
    (hu : IsSpecialVector m u) (hA4 : u.val.2 0 7=0) (hC4 : u.val.2 2 7=0)
    (hB3 : u.val.2 1 6=0) (hB4 : u.val.2 1 7=0)
    (hC3 : u.val.2 2 6≠0) : u.val.2 1 5=0 := by
  have h := hu.specialAdjoint9_zero
  change u.val.1 0 * u.val.2 0 7 + u.val.2 1 4 * u.val.2 2 7 +
    u.val.2 1 5 * u.val.2 2 6 + u.val.2 1 6 * u.val.2 2 5 +
    u.val.2 1 7 * u.val.2 2 3 = 0 at h
  simp only [hA4,hC4,hB3,hB4,
    mul_zero,zero_mul,zero_add,add_zero] at h
  exact (mul_eq_zero.mp h).resolve_right hC3

/-- Once C2 is removed, the second checked adjoint coordinate forces A2=0. -/
theorem IsSpecialVector.A2_zero_of_reduced_C3 {m : ℕ} {u : TraceZero F}
    (hu : IsSpecialVector m u) (hA4 : u.val.2 0 7=0) (hC4 : u.val.2 2 7=0)
    (hB4 : u.val.2 1 7=0) (hC2 : u.val.2 2 5=0)
    (hC3 : u.val.2 2 6≠0) : u.val.2 0 5=0 := by
  have h := hu.specialAdjoint17_zero
  change u.val.1 1 * u.val.2 1 7 + u.val.2 0 3 * u.val.2 2 7 +
    u.val.2 0 5 * u.val.2 2 6 + u.val.2 0 6 * u.val.2 2 5 +
    u.val.2 0 7 * u.val.2 2 4 = 0 at h
  simp only [hA4,hC4,hB4,hC2,
    mul_zero,zero_mul,zero_add,add_zero] at h
  exact (mul_eq_zero.mp h).resolve_right hC3

/-- Strict absolute-grade descent from C3 (grade8) to at most C2 (grade5).
A2 remains nonzero. The stronger assertion that C2 vanishes is not assumed. -/
theorem specialVector_C3_strict_descent {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) {u : TraceZero F}
    (hu : IsSpecialVector m u) (hA4 : u.val.2 0 7=0) (hC4 : u.val.2 2 7=0)
    (hB3 : u.val.2 1 6=0) (hB4 : u.val.2 1 7=0)
    (hC3 : u.val.2 2 6≠0) :
    let z := (thirdPivotDescent hcard u).val u
    IsSpecialVector m z ∧ z.val.2 0 7=0 ∧ z.val.2 2 7=0 ∧
      z.val.2 1 7=0 ∧ z.val.2 1 6=0 ∧ z.val.2 2 6=0 ∧
      z.val.2 1 5=0 ∧ z.val.2 0 6=0 ∧ z.val.2 0 5=u.val.2 2 6 ∧
      z.val.2 0 5≠0 := by
  let w := (thirdPivot hcard u).val u
  have hw : IsSpecialVector m w := hu.map_model (thirdPivot hcard u)
  have ha : w.val.2 0 7=0 := hA4
  have hc4 : w.val.2 2 7=0 := by
    change u.val.2 2 7 + thirdPivotParameter m u*u.val.2 0 7=0
    rw [hC4,hA4,mul_zero,add_zero]
  have hb3 : w.val.2 1 6=0 := hB3
  have hb4 : w.val.2 1 7=0 := hB4
  have hc3 : w.val.2 2 6≠0 := hC3
  have hc2 : w.val.2 2 5=0 := thirdPivot_C2_zero hcard u hC3
  have hb2 : w.val.2 1 5=0 := hw.B2_zero_of_leading_C3 ha hc4 hb3 hb4 hc3
  have ha2 : w.val.2 0 5=0 := hw.A2_zero_of_reduced_C3 ha hc4 hb4 hc2 hc3
  refine ⟨hu.map_model (thirdPivotDescent hcard u),hc4,ha,hb4,hb2,ha2,hb3,hc2,?_,?_⟩
  · rfl
  · exact hc3
end Atlas.ReeF4
