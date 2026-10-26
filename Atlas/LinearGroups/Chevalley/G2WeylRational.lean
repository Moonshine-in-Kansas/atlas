import Atlas.Algebra.WeylOperatorPinningThree
import Atlas.LinearGroups.Chevalley.Integral.UniformLoweringStrings
import Atlas.LinearGroups.Chevalley.A2WeylRational

/-! The actual triple-edge Weyl pinning over rational coefficient algebras.
The numerator and lowering coefficients are proved over Z first. -/

noncomputable section
namespace Atlas.Chevalley.Integral
attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)

include hdiamond

/-- The integral 3,4,3 operator string survives every coefficient reduction. -/
theorem raisingOver_g2_weyl_string (R : Type*) [CommRing R]
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = -3) :
    let A := raisingOver P b R i
    let B := raisingOver P b R j
    let F := loweringOver P b R i
    let C := A * B - B * A
    let D := A * C - C * A
    let L := A * D - D * A
    Commute A L ∧ Commute F B ∧
      F * C - C * F = (3 : ℤ) • B ∧
      F * D - D * F = (4 : ℤ) • C ∧
      F * L - L * F = (3 : ℤ) • D := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let F := loweringOver P b R i
  let C := A * B - B * A
  let D := A * C - C * A
  let L := A * D - D * A
  change Commute A L ∧ Commute F B ∧
    F * C - C * F = (3 : ℤ) • B ∧ F * D - D * F = (4 : ℤ) • C ∧
    F * L - L * F = (3 : ℤ) • D
  have hAL : Commute A L := by
    have h := congrArg (Int.castRingHom R).mapMatrix
      (raising_g2_serre P b hdiamond i j hne hji)
    simp only [Ring.lie_def, map_sub, map_mul, map_zero] at h
    apply sub_eq_zero.mp
    simpa only [A, B, C, D, L, raisingOver, RingHom.mapMatrix_apply] using h
  have hFB : Commute F B := by
    have h := congrArg (Int.castRingHom R).mapMatrix
      (raising_lowering_commute_of_diamond P b hdiamond j i hne.symm).symm.eq
    simp only [map_mul] at h
    simpa only [F, B, raisingOver, loweringOver, RingHom.mapMatrix_apply,
      Commute, SemiconjBy] using h
  obtain ⟨hc, hd, hl⟩ := lowering_g2_operator_string P b hdiamond i j hne hji
  refine ⟨hAL, hFB, ?_, ?_, ?_⟩
  · have h := congrArg (Int.castRingHom R).mapMatrix hc
    simp only [Ring.lie_def, map_sub, map_mul, map_zsmul] at h
    simpa only [A, B, C, F, raisingOver, loweringOver, RingHom.mapMatrix_apply] using h
  · have h := congrArg (Int.castRingHom R).mapMatrix hd
    simp only [Ring.lie_def, map_sub, map_mul, map_zsmul] at h
    simpa only [A, B, C, D, F, raisingOver, loweringOver, RingHom.mapMatrix_apply] using h
  · have h := congrArg (Int.castRingHom R).mapMatrix hl
    simp only [Ring.lie_def, map_sub, map_mul, map_zsmul] at h
    simpa only [A, B, C, D, L, F, raisingOver, loweringOver,
      RingHom.mapMatrix_apply] using h

end Atlas.Chevalley.Integral

namespace Atlas.Chevalley
open Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R] [Algebra ℚ R]

include hdiamond

/-- The actual Weyl word sends the bottom triple-edge operator to its
third raised operator divided by 3!, over a rational coefficient algebra. -/
theorem adjointWeyl_one_conjugate_raisingOver_g2
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = -3) :
    let A := raisingOver P b R i
    let B := raisingOver P b R j
    let C := A * B - B * A
    let D := A * C - C * A
    (adjointWeyl P b R i 1).val.val * B *
      ((adjointWeyl P b R i 1)⁻¹).val.val =
        (1 / 6 : ℚ) • (A * D - D * A) := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let F := loweringOver P b R i
  let C := A * B - B * A
  let D := A * C - C * A
  let L := A * D - D * A
  obtain ⟨hAL, hFB, hFC, hFD, hFL⟩ :=
    raisingOver_g2_weyl_string P b hdiamond R i j hne hji
  have hFCQ : F * C - C * F = (3 : ℚ) • B := by
    calc
      _ = (3 : ℤ) • B := hFC
      _ = (3 : ℚ) • B := by
        simpa only [Int.cast_ofNat] using (Int.cast_smul_eq_zsmul ℚ (3 : ℤ) B).symm
  have hFDQ : F * D - D * F = (4 : ℚ) • C := by
    calc
      _ = (4 : ℤ) • C := hFD
      _ = (4 : ℚ) • C := by
        simpa only [Int.cast_ofNat] using (Int.cast_smul_eq_zsmul ℚ (4 : ℤ) C).symm
  have hFLQ : F * L - L * F = (3 : ℚ) • D := by
    calc
      _ = (3 : ℤ) • D := hFL
      _ = (3 : ℚ) • D := by
        simpa only [Int.cast_ofNat] using (Int.cast_smul_eq_zsmul ℚ (3 : ℤ) D).symm
  have hpin := Atlas.Algebra.weyl_word_conjugate_operator_eq_sixth A F B C D L
    (raisingOver_nilpotent P b R i) (loweringOver_nilpotent P b R i)
    rfl rfl rfl hAL hFB hFCQ hFDQ hFLQ
  let e : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ :=
    ⟨IsNilpotent.exp A, IsNilpotent.exp (-A),
      IsNilpotent.exp_mul_exp_neg_self (raisingOver_nilpotent P b R i),
      IsNilpotent.exp_neg_mul_exp_self (raisingOver_nilpotent P b R i)⟩
  let f : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ :=
    ⟨IsNilpotent.exp F, IsNilpotent.exp (-F),
      IsNilpotent.exp_mul_exp_neg_self (loweringOver_nilpotent P b R i),
      IsNilpotent.exp_neg_mul_exp_self (loweringOver_nilpotent P b R i)⟩
  have hw : (adjointWeyl P b R i 1).val = e * f⁻¹ * e := by
    apply Units.ext
    change raisingExponential P b R i 1 * (loweringRootElement P b R i (-1)).val *
        raisingExponential P b R i 1 =
      IsNilpotent.exp A * IsNilpotent.exp (-F) * IsNilpotent.exp A
    simp only [A, F, loweringRootElement_val, raisingExponential_eq_nilpotent_exp,
      loweringExponential_eq_nilpotent_exp, one_smul, neg_one_smul]
  change (adjointWeyl P b R i 1).val.val * B *
    ((adjointWeyl P b R i 1).val⁻¹).val = (1 / 6 : ℚ) • L
  rw [hw]
  change (IsNilpotent.exp A * IsNilpotent.exp (-F) * IsNilpotent.exp A) * B *
    (IsNilpotent.exp (-A) * (IsNilpotent.exp F * IsNilpotent.exp (-A))) = (1 / 6 : ℚ) • L
  simpa only [mul_assoc] using hpin

end Atlas.Chevalley
