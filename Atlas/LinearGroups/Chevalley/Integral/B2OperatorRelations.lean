import Atlas.LinearGroups.Chevalley.Integral.B2IntegralSerre
import Mathlib.Tactic.Abel

/-! UNCOMPILED source candidate. Actual double-edge Geck operator
relations, proved integrally first and then reduced to any commutative ring. -/

noncomputable section
namespace Atlas.Chevalley.Integral

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R]

include hdiamond

/-- With i short and j long, the actual two-step raising bracket D commutes
with A,B,C. Both lowering coefficients are two, in every target characteristic. -/
theorem raisingOver_b2_operator_relations
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    let A := raisingOver P b R i
    let B := raisingOver P b R j
    let F := loweringOver P b R i
    let C := A * B - B * A
    let D := A * C - C * A
    Commute A D ∧ Commute B C ∧ Commute B D ∧ Commute C D ∧
      F * C - C * F = (2 : R) • B ∧ F * D - D * F = (2 : R) • C := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let F := loweringOver P b R i
  let C := A * B - B * A
  let D := A * C - C * A
  change Commute A D ∧ Commute B C ∧ Commute B D ∧ Commute C D ∧
    F * C - C * F = (2 : R) • B ∧ F * D - D * F = (2 : R) • C
  have hAD : Commute A D := by
    have h := congrArg (Int.castRingHom R).mapMatrix
      (raising_b2_serre P b hdiamond i j hne hji)
    simp only [Ring.lie_def, map_sub, map_mul, map_zero] at h
    apply sub_eq_zero.mp
    simpa only [A, B, C, D, raisingOver, RingHom.mapMatrix_apply] using h
  have hBC : Commute B C := by
    have h := congrArg (Int.castRingHom R).mapMatrix
      (raising_a2_commute_bracket_right P b hdiamond i j hne hij).eq
    simp only [map_mul, map_sub] at h
    simpa only [A, B, C, raisingOver, RingHom.mapMatrix_apply, Commute, SemiconjBy] using h
  have hBA : ⁅B, A⁆ = -C := by
    change B * A - A * B = -(A * B - B * A)
    abel
  have hBCzero : ⁅B, C⁆ = 0 := sub_eq_zero.mpr hBC.eq
  have hADzero : ⁅A, D⁆ = 0 := sub_eq_zero.mpr hAD.eq
  have hBDzero : ⁅B, D⁆ = 0 := by
    change ⁅B, ⁅A, C⁆⁆ = 0
    rw [leibniz_lie, hBA, hBCzero, neg_lie, lie_self, neg_zero, lie_zero, add_zero]
  have hCDzero : ⁅C, D⁆ = 0 := by
    change ⁅⁅A, B⁆, D⁆ = 0
    rw [lie_lie, hBDzero, hADzero, lie_zero, lie_zero, sub_self]
  refine ⟨hAD, hBC, sub_eq_zero.mp hBDzero, sub_eq_zero.mp hCDzero, ?_, ?_⟩
  · have h := congrArg (Int.castRingHom R).mapMatrix
      (lowering_b2_bracket_eq_two_raising P b hdiamond i j hne hji)
    simp only [Ring.lie_def, two_smul, map_sub, map_mul, map_add] at h
    simpa only [A, B, C, F, raisingOver, loweringOver, RingHom.mapMatrix_apply,
      two_smul] using h
  · have h := congrArg (Int.castRingHom R).mapMatrix
      (lowering_b2_double_bracket_eq_two_bracket P b hdiamond i j hne hji)
    simp only [Ring.lie_def, two_smul, map_sub, map_mul, map_add] at h
    simpa only [A, B, C, D, F, raisingOver, loweringOver, RingHom.mapMatrix_apply,
      two_smul] using h

end Atlas.Chevalley.Integral
