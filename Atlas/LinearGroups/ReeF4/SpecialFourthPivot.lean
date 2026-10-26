import Atlas.LinearGroups.ReeF4.RootGroupMembership
import Atlas.LinearGroups.ReeF4.WeylModel
import Atlas.LinearGroups.ReeF4.SpecialVectors

noncomputable section
set_option maxRecDepth 4096
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def fourthPivotA (m : ℕ) (u : TraceZero F) : F :=
  thetaInv F m (u.val.2 2 3 / u.val.2 2 5)
def fourthPivotB (u : TraceZero F) : F := u.val.2 1 4 / u.val.2 2 5

def fourthPivot {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (u : TraceZero F) : Model F m :=
  ⟨shortRootPairEquiv m hcard (fourthPivotA m u) (fourthPivotB u),
    shortRootPairEquiv_mem_modelSubgroup hcard _ _⟩

def fourthPivotDescent {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (u : TraceZero F) : Model F m :=
  ⟨weylRho,weylOperator_mem_modelSubgroup m 0⟩ * fourthPivot hcard u

theorem fourthPivot_Cminus1_zero {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u : TraceZero F)
    (hB2 : u.val.2 1 5=0) (hC2 : u.val.2 2 5≠0) :
    ((fourthPivot hcard u).val u).val.2 2 3=0 := by
  change (u.val.2 2 3 + fourthPivotB u*u.val.2 1 5) +
    theta F m (fourthPivotA m u)*u.val.2 2 5=0
  simp only [hB2,mul_zero,add_zero,fourthPivotA,theta_thetaInv hcard]
  rw [div_mul_cancel₀ _ hC2,CharTwo.add_self_eq_zero]

theorem fourthPivot_B1_zero {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u : TraceZero F)
    (hB2 : u.val.2 1 5=0) (hC2 : u.val.2 2 5≠0) :
    ((fourthPivot hcard u).val u).val.2 1 4=0 := by
  have ha : theta F m (fourthPivotA m u)*u.val.2 2 5=u.val.2 2 3 := by
    rw [fourthPivotA,theta_thetaInv hcard,div_mul_cancel₀ _ hC2]
  have hb : fourthPivotB u*u.val.2 2 5=u.val.2 1 4 := div_mul_cancel₀ _ hC2
  change (u.val.2 1 4 + theta F m (fourthPivotB u)*u.val.2 1 5 +
    fourthPivotB u*u.val.2 2 5) +
    (fourthPivotA m u)^2*theta F m (fourthPivotA m u)*u.val.2 1 5 +
    fourthPivotA m u*(u.val.2 2 3+fourthPivotB u*u.val.2 1 5) +
    fourthPivotA m u*theta F m (fourthPivotA m u)*u.val.2 2 5=0
  simp only [hB2,mul_zero,add_zero,hb]
  rw [mul_assoc,ha,CharTwo.add_self_eq_zero,zero_add,CharTwo.add_self_eq_zero]

/-- A genuine extra reduction case, without assuming that inner-root leading
coordinates are impossible. It lowers grade5 to at most4 and retains C−1≠0. -/
theorem specialVector_C2_strict_descent {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) {u : TraceZero F}
    (hu : IsSpecialVector m u) (hA4 : u.val.2 0 7=0) (hC4 : u.val.2 2 7=0)
    (hB4 : u.val.2 1 7=0) (hB3 : u.val.2 1 6=0) (hC3 : u.val.2 2 6=0)
    (hB2 : u.val.2 1 5=0) (hA3 : u.val.2 0 6=0) (hC2 : u.val.2 2 5≠0) :
    let z := (fourthPivotDescent hcard u).val u
    IsSpecialVector m z ∧ z.val.2 0 7=0 ∧ z.val.2 2 7=0 ∧
      z.val.2 1 7=0 ∧ z.val.2 1 6=0 ∧ z.val.2 2 6=0 ∧
      z.val.2 1 5=0 ∧ z.val.2 0 6=0 ∧ z.val.2 2 5=0 ∧
      z.val.2 2 3=u.val.2 2 5 ∧ z.val.2 2 3≠0 := by
  let w := (fourthPivot hcard u).val u
  have hwa : w.val.2 0 7=0 := hA4
  have hwc4 : w.val.2 2 7=0 := hC4
  have hwb4 : w.val.2 1 7=0 := by
    change u.val.2 1 7+fourthPivotA m u*u.val.2 2 7=0
    simp only [hB4,hC4,mul_zero,add_zero]
  have hwb3 : w.val.2 1 6=0 := by
    change (u.val.2 1 6+fourthPivotB u*u.val.2 2 7)+
      theta F m (fourthPivotA m u)*u.val.2 1 7=0
    simp only [hB3,hB4,hC4,mul_zero,add_zero]
  have hwc3 : w.val.2 2 6=0 := by
    change (u.val.2 2 6+fourthPivotB u*u.val.2 1 7+
      theta F m (fourthPivotB u)*u.val.2 2 7)+
      fourthPivotA m u*(u.val.2 1 6+fourthPivotB u*u.val.2 2 7)+
      fourthPivotA m u*theta F m (fourthPivotA m u)*u.val.2 1 7+
      (fourthPivotA m u)^2*theta F m (fourthPivotA m u)*u.val.2 2 7=0
    simp only [hC3,hB3,hB4,hC4,mul_zero,zero_add,add_zero]
  have hwb1 : w.val.2 1 4=0 := fourthPivot_B1_zero hcard u hB2 hC2
  have hwcm1 : w.val.2 2 3=0 := fourthPivot_Cminus1_zero hcard u hB2 hC2
  have hwc2 : w.val.2 2 5=u.val.2 2 5 := by
    change u.val.2 2 5+fourthPivotA m u*u.val.2 1 5=u.val.2 2 5
    rw [hB2,mul_zero,add_zero]
  refine ⟨hu.map_model (fourthPivotDescent hcard u),hwa,hwc3,hwb3,hwb4,hwc4,
    hwb1,hA3,hwcm1,hwc2,?_⟩
  change w.val.2 2 5 ≠ 0
  rw [hwc2]
  exact hC2
end Atlas.ReeF4
