import Atlas.LinearGroups.ReeF4.SpecialAdjoint
import Atlas.LinearGroups.ReeF4.RootGroupMembership
import Atlas.LinearGroups.ReeF4.WeylModel

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Rank-one conditions exclude C−1,B1 and the first actual diagonal when A2
is leading. The third assertion is about actualDiag0, not marked d0. -/
theorem IsSpecialVector.A2_adjacent_coordinates_zero {m : ℕ} {u : TraceZero F}
    (hu : IsSpecialVector m u) (hA4 : u.val.2 0 7=0) (hC4 : u.val.2 2 7=0)
    (hB4 : u.val.2 1 7=0) (hB2 : u.val.2 1 5=0) (hC2 : u.val.2 2 5=0)
    (hA2 : u.val.2 0 5≠0) :
    u.val.2 2 3=0 ∧ u.val.2 1 4=0 ∧ u.val.1 0=0 := by
  have h15 : fullAdjointRoot15 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot15_actual,hu.adjoint_zero]; rfl
  change u.val.1 1*u.val.2 1 5 + u.val.2 0 1*u.val.2 2 7 +
    u.val.2 0 4*u.val.2 2 5 + u.val.2 0 5*u.val.2 2 3 +
    u.val.2 0 7*u.val.2 2 1=0 at h15
  simp only [hB2,hC4,hC2,hA4,mul_zero,zero_mul,zero_add,add_zero] at h15
  have hc : u.val.2 2 3=0 := (mul_eq_zero.mp h15).resolve_left hA2
  have h23 : fullAdjointRoot23 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot23_actual,hu.adjoint_zero]; rfl
  change u.val.1 1*u.val.2 2 5 + u.val.1 0*u.val.2 2 5 +
    u.val.2 0 1*u.val.2 1 7 + u.val.2 0 3*u.val.2 1 5 +
    u.val.2 0 5*u.val.2 1 4 + u.val.2 0 7*u.val.2 1 1=0 at h23
  simp only [hC2,hB4,hB2,hA4,mul_zero,zero_mul,zero_add,add_zero] at h23
  have hb : u.val.2 1 4=0 := (mul_eq_zero.mp h23).resolve_left hA2
  have h7 : fullAdjointRoot7 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot7_actual,hu.adjoint_zero]; rfl
  change u.val.1 0*u.val.2 0 5 + u.val.2 1 1*u.val.2 2 7 +
    u.val.2 1 3*u.val.2 2 5 + u.val.2 1 5*u.val.2 2 4 +
    u.val.2 1 7*u.val.2 2 1=0 at h7
  simp only [hC4,hC2,hB2,hB4,mul_zero,zero_mul,zero_add,add_zero] at h7
  exact ⟨hc,hb,(mul_eq_zero.mp h7).resolve_right hA2⟩

def fifthPivotA (m : ℕ) (u : TraceZero F) : F := thetaInv F m (u.val.2 0 4/u.val.2 0 5)
def fifthPivotB (u : TraceZero F) : F := u.val.1 1/u.val.2 0 5

def fifthPivot {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (u : TraceZero F) : Model F m :=
  ⟨shortRootPairEquiv m hcard (fifthPivotA m u) (fifthPivotB u),
    shortRootPairEquiv_mem_modelSubgroup hcard _ _⟩

def fifthPivotDescent {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (u : TraceZero F) : Model F m :=
  ⟨weylRho,weylOperator_mem_modelSubgroup m 0⟩ * fifthPivot hcard u

theorem fifthPivot_A1_zero {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (u : TraceZero F) (ha : u.val.2 0 5≠0) : ((fifthPivot hcard u).val u).val.2 0 4=0 := by
  change u.val.2 0 4+theta F m (thetaInv F m (u.val.2 0 4/u.val.2 0 5))*u.val.2 0 5=0
  rw [theta_thetaInv hcard,div_mul_cancel₀ _ ha,CharTwo.add_self_eq_zero]

theorem fifthPivot_diag1_zero {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (u : TraceZero F) (ha : u.val.2 0 5≠0) : ((fifthPivot hcard u).val u).val.1 1=0 := by
  have ht : theta F m (fifthPivotA m u)*u.val.2 0 5=u.val.2 0 4 := by
    rw [fifthPivotA,theta_thetaInv hcard,div_mul_cancel₀ _ ha]
  have hb : fifthPivotB u*u.val.2 0 5=u.val.1 1 := div_mul_cancel₀ _ ha
  change (u.val.1 1+fifthPivotB u*u.val.2 0 5) +
    fifthPivotA m u*u.val.2 0 4 + fifthPivotA m u*theta F m (fifthPivotA m u)*u.val.2 0 5=0
  rw [hb,CharTwo.add_self_eq_zero,zero_add,mul_assoc,ht,CharTwo.add_self_eq_zero]

/-- Explicit A2-to-lower-grade reduction; the possible residual A1 is left
visible rather than assuming the source's eight-leading-root classification. -/
theorem specialVector_A2_strict_descent {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) {u : TraceZero F}
    (hu : IsSpecialVector m u) (hA4 : u.val.2 0 7=0) (hC4 : u.val.2 2 7=0)
    (hB4 : u.val.2 1 7=0) (hB3 : u.val.2 1 6=0) (hC3 : u.val.2 2 6=0)
    (hB2 : u.val.2 1 5=0) (hA3 : u.val.2 0 6=0) (hC2 : u.val.2 2 5=0)
    (hA2 : u.val.2 0 5≠0) :
    let z := (fifthPivotDescent hcard u).val u
    IsSpecialVector m z ∧ z.val.2 0 7=0 ∧ z.val.2 2 7=0 ∧
      z.val.2 1 7=0 ∧ z.val.2 1 6=0 ∧ z.val.2 2 6=0 ∧
      z.val.2 1 5=0 ∧ z.val.2 0 6=0 ∧ z.val.2 2 5=0 ∧
      z.val.2 0 5=0 ∧ z.val.2 2 3=0 ∧ z.val.2 1 4=0 ∧
      z.val.1 0=0 ∧ z.val.1 1=0 ∧ z.val.2 0 2=u.val.2 0 5 ∧ z.val.2 0 2≠0 := by
  obtain ⟨hCm1,hB1,hD0⟩ := hu.A2_adjacent_coordinates_zero hA4 hC4 hB4 hB2 hC2 hA2
  let w := (fifthPivot hcard u).val u
  have hw := hu.map_model (fifthPivot hcard u)
  have hwa4 : w.val.2 0 7=0 := hA4
  have hwc4 : w.val.2 2 7=0 := hC4
  have hwa3 : w.val.2 0 6=0 := hA3
  have hwb2 : w.val.2 1 5=0 := hB2
  have hwd0 : w.val.1 0=0 := hD0
  have hwa2 : w.val.2 0 5=u.val.2 0 5 := rfl
  have hwb4 : w.val.2 1 7=0 := by
    change u.val.2 1 7+fifthPivotA m u*u.val.2 2 7=0
    simp only [hB4,hC4,mul_zero,add_zero]
  have hwb3 : w.val.2 1 6=0 := by
    change (u.val.2 1 6+fifthPivotB u*u.val.2 2 7)+theta F m (fifthPivotA m u)*u.val.2 1 7=0
    simp only [hB3,hB4,hC4,mul_zero,add_zero]
  have hwc3 : w.val.2 2 6=0 := by
    change (u.val.2 2 6+fifthPivotB u*u.val.2 1 7+theta F m (fifthPivotB u)*u.val.2 2 7)+
      fifthPivotA m u*(u.val.2 1 6+fifthPivotB u*u.val.2 2 7)+
      fifthPivotA m u*theta F m (fifthPivotA m u)*u.val.2 1 7+
      (fifthPivotA m u)^2*theta F m (fifthPivotA m u)*u.val.2 2 7=0
    simp only [hC3,hB3,hB4,hC4,mul_zero,zero_add,add_zero]
  have hwc2 : w.val.2 2 5=0 := by
    change u.val.2 2 5+fifthPivotA m u*u.val.2 1 5=0
    simp only [hC2,hB2,mul_zero,add_zero]
  have hwcm1 : w.val.2 2 3=0 := by
    change (u.val.2 2 3+fifthPivotB u*u.val.2 1 5)+theta F m (fifthPivotA m u)*u.val.2 2 5=0
    simp only [hCm1,hB2,hC2,mul_zero,add_zero]
  have hwb1 : w.val.2 1 4=0 := by
    change (u.val.2 1 4+theta F m (fifthPivotB u)*u.val.2 1 5+fifthPivotB u*u.val.2 2 5)+
      (fifthPivotA m u)^2*theta F m (fifthPivotA m u)*u.val.2 1 5+
      fifthPivotA m u*(u.val.2 2 3+fifthPivotB u*u.val.2 1 5)+
      fifthPivotA m u*theta F m (fifthPivotA m u)*u.val.2 2 5=0
    simp only [hB1,hB2,hC2,hCm1,mul_zero,zero_add,add_zero]
  have hwa1 : w.val.2 0 4=0 := fifthPivot_A1_zero hcard u hA2
  have hwd1 : w.val.1 1=0 := fifthPivot_diag1_zero hcard u hA2
  have hwam2 : w.val.2 0 2=0 := by
    have h := congrArg (fun x : Carrier F => x.1 0) hw.adjoint_zero
    change w.val.1 1*w.val.1 2 - (w.val.2 0 0*w.val.2 0 7+
      w.val.2 0 1*w.val.2 0 6+w.val.2 0 2*w.val.2 0 5+w.val.2 0 3*w.val.2 0 4)=0 at h
    simp only [hwd1,hwa4,hwa3,hwa1,mul_zero,zero_mul,zero_add,add_zero,zero_sub] at h
    have hp := neg_eq_zero.mp h
    exact (mul_eq_zero.mp hp).resolve_right (by rw [hwa2]; exact hA2)
  refine ⟨hu.map_model (fifthPivotDescent hcard u),hwa4,hwc3,hwb3,hwb4,hwc4,
    hwb1,hwa3,hwcm1,hwam2,hwc2,hwb2,hwd0,hwd1,hwa2,?_⟩
  change w.val.2 0 5 ≠ 0
  rw [hwa2]
  exact hA2
end Atlas.ReeF4
