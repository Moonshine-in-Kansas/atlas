import Atlas.LinearGroups.Chevalley.Integral.UniformIntegralSerre
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-! Source candidate: the actual triple-edge raising operators satisfy the
six-positive-root bracket configuration. The only cancellation of 2 occurs
in integer matrices, before coefficient reduction to an arbitrary ring. -/

noncomputable section
namespace Atlas.Chevalley.Integral

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)

include hdiamond

/-- All required cross-brackets in the actual integral triple edge. Here
`i` is short, `j` is long, and `F=[B,L]` is the highest-root bracket. -/
theorem raising_g2_cross_brackets
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    let A := raising P b i
    let B := raising P b j
    let C := A * B - B * A
    let D := A * C - C * A
    let L := A * D - D * A
    let F := B * L - L * B
    Commute A L ∧ Commute B C ∧ Commute B D ∧
      C * D - D * C = -F ∧ Commute C L ∧ Commute D L ∧
      Commute A F ∧ Commute B F ∧ Commute C F ∧
      Commute D F ∧ Commute L F := by
  let A := raising P b i
  let B := raising P b j
  let C := A * B - B * A
  let D := A * C - C * A
  let L := A * D - D * A
  let F := B * L - L * B
  change Commute A L ∧ Commute B C ∧ Commute B D ∧
    C * D - D * C = -F ∧ Commute C L ∧ Commute D L ∧
    Commute A F ∧ Commute B F ∧ Commute C F ∧
    Commute D F ∧ Commute L F
  have hAL : ⁅A, L⁆ = 0 := raising_g2_serre P b hdiamond i j hne hji
  have hBC : ⁅B, C⁆ = 0 :=
    sub_eq_zero.mpr (raising_a2_commute_bracket_right P b hdiamond i j hne hij).eq
  have hBA : ⁅B, A⁆ = -C := by
    change B * A - A * B = -(A * B - B * A)
    abel
  have hBD : ⁅B, D⁆ = 0 := by
    change ⁅B, ⁅A, C⁆⁆ = 0
    rw [leibniz_lie, hBA, hBC, neg_lie, lie_self, neg_zero, lie_zero, add_zero]
  have hCD : ⁅C, D⁆ = -F := by
    change ⁅⁅A, B⁆, D⁆ = -⁅B, ⁅A, D⁆⁆
    rw [lie_lie, hBD, lie_zero, zero_sub]
  have hAF : ⁅A, F⁆ = ⁅C, L⁆ := by
    change ⁅A, ⁅B, L⁆⁆ = ⁅⁅A, B⁆, L⁆
    rw [leibniz_lie, hAL, lie_zero, add_zero]
  have hCLneg : ⁅C, L⁆ = -⁅C, L⁆ := by
    have h := congrArg (fun X => ⁅A, X⁆) hCD
    rw [leibniz_lie, lie_neg] at h
    change ⁅D, D⁆ + ⁅C, L⁆ = -⁅A, F⁆ at h
    simpa only [lie_self, zero_add, hAF] using h
  have hCLtwo : (2 : ℤ) • ⁅C, L⁆ = 0 := by
    rw [two_smul]
    calc
      ⁅C, L⁆ + ⁅C, L⁆ = -⁅C, L⁆ + ⁅C, L⁆ :=
        congrArg (fun X => X + ⁅C, L⁆) hCLneg
      _ = 0 := neg_add_cancel _
  have hCL : ⁅C, L⁆ = 0 := by
    apply (smul_right_injective
      (M := Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
      (show (2 : ℤ) ≠ 0 by norm_num))
    simpa only [smul_zero] using hCLtwo
  have hDL : ⁅D, L⁆ = 0 := by
    change ⁅⁅A, C⁆, L⁆ = 0
    rw [lie_lie, hCL, hAL, lie_zero, lie_zero, sub_self]
  have hAFzero : ⁅A, F⁆ = 0 := hAF.trans hCL
  have hBF : ⁅B, F⁆ = 0 := by
    have h := congrArg (fun X => ⁅B, X⁆) hCD
    rw [leibniz_lie, hBC, hBD, zero_lie, lie_zero, zero_add, lie_neg] at h
    exact neg_eq_zero.mp h.symm
  have hCF : ⁅C, F⁆ = 0 := by
    change ⁅⁅A, B⁆, F⁆ = 0
    rw [lie_lie, hBF, hAFzero, lie_zero, lie_zero, sub_self]
  have hDF : ⁅D, F⁆ = 0 := by
    change ⁅⁅A, C⁆, F⁆ = 0
    rw [lie_lie, hCF, hAFzero, lie_zero, lie_zero, sub_self]
  have hLF : ⁅L, F⁆ = 0 := by
    change ⁅⁅A, D⁆, F⁆ = 0
    rw [lie_lie, hDF, hAFzero, lie_zero, lie_zero, sub_self]
  exact ⟨sub_eq_zero.mp hAL, sub_eq_zero.mp hBC, sub_eq_zero.mp hBD,
    hCD, sub_eq_zero.mp hCL, sub_eq_zero.mp hDL,
    sub_eq_zero.mp hAFzero, sub_eq_zero.mp hBF, sub_eq_zero.mp hCF,
    sub_eq_zero.mp hDF, sub_eq_zero.mp hLF⟩

variable (R : Type*) [CommRing R]

/-- The triple-edge cross-brackets survive coefficient reduction, including
characteristics 2 and 3. There is no cancellation in the target ring. -/
theorem raisingOver_g2_cross_brackets
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    let A := raisingOver P b R i
    let B := raisingOver P b R j
    let C := A * B - B * A
    let D := A * C - C * A
    let L := A * D - D * A
    let F := B * L - L * B
    Commute A L ∧ Commute B C ∧ Commute B D ∧
      C * D - D * C = -F ∧ Commute C L ∧ Commute D L ∧
      Commute A F ∧ Commute B F ∧ Commute C F ∧
      Commute D F ∧ Commute L F := by
  obtain ⟨hAL, hBC, hBD, hCD, hCL, hDL, hAF, hBF, hCF, hDF, hLF⟩ :=
    raising_g2_cross_brackets P b hdiamond i j hne hij hji
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hAL.map (Int.castRingHom R).mapMatrix
    simpa only [map_mul, map_sub, raisingOver, RingHom.mapMatrix_apply] using h
  · have h := hBC.map (Int.castRingHom R).mapMatrix
    simpa only [map_mul, map_sub, raisingOver, RingHom.mapMatrix_apply] using h
  · have h := hBD.map (Int.castRingHom R).mapMatrix
    simpa only [map_mul, map_sub, raisingOver, RingHom.mapMatrix_apply] using h
  · have h := congrArg (Int.castRingHom R).mapMatrix hCD
    simpa only [map_mul, map_sub, map_neg, raisingOver,
      RingHom.mapMatrix_apply] using h
  · have h := hCL.map (Int.castRingHom R).mapMatrix
    simpa only [map_mul, map_sub, raisingOver, RingHom.mapMatrix_apply] using h
  · have h := hDL.map (Int.castRingHom R).mapMatrix
    simpa only [map_mul, map_sub, raisingOver, RingHom.mapMatrix_apply] using h
  · have h := hAF.map (Int.castRingHom R).mapMatrix
    simpa only [map_mul, map_sub, raisingOver, RingHom.mapMatrix_apply] using h
  · have h := hBF.map (Int.castRingHom R).mapMatrix
    simpa only [map_mul, map_sub, raisingOver, RingHom.mapMatrix_apply] using h
  · have h := hCF.map (Int.castRingHom R).mapMatrix
    simpa only [map_mul, map_sub, raisingOver, RingHom.mapMatrix_apply] using h
  · have h := hDF.map (Int.castRingHom R).mapMatrix
    simpa only [map_mul, map_sub, raisingOver, RingHom.mapMatrix_apply] using h
  · have h := hLF.map (Int.castRingHom R).mapMatrix
    simpa only [map_mul, map_sub, raisingOver, RingHom.mapMatrix_apply] using h

end Atlas.Chevalley.Integral
