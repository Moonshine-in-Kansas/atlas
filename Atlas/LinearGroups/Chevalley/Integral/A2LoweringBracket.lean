import Atlas.LinearGroups.Chevalley.Integral.LocalDiamondCommutation

/-! The actual integral lowering action on a single-edge raising bracket.
The Cartan condition is row j, column i. -/

noncomputable section

namespace Atlas.Chevalley.Integral

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)

include hdiamond

/-- Jacobi and the actual Geck relations give [F_i,[E_i,E_j]]=E_j integrally. -/
theorem lowering_a2_bracket_eq_raising (i j : b.support) (hne : i ≠ j)
    (hji : b.cartanMatrix j i = -1) :
    lowering P b i * (raising P b i * raising P b j - raising P b j * raising P b i) -
      (raising P b i * raising P b j - raising P b j * raising P b i) *
        lowering P b i = raising P b j := by
  have hFE : ⁅lowering P b i, raising P b i⁆ =
      -RootPairing.GeckConstruction.h i := by
    change ⁅RootPairing.GeckConstruction.f i, RootPairing.GeckConstruction.e i⁆ = _
    rw [← lie_skew, RootPairing.GeckConstruction.lie_e_f_same]
  have hFB : ⁅lowering P b i, raising P b j⁆ = 0 := by
    change lowering P b i * raising P b j - raising P b j * lowering P b i = 0
    exact sub_eq_zero.mpr
      (raising_lowering_commute_of_diamond P b hdiamond j i hne.symm).symm.eq
  have hHB : ⁅RootPairing.GeckConstruction.h i, raising P b j⁆ =
      -raising P b j := by
    simpa only [hji, neg_one_smul] using
      (RootPairing.GeckConstruction.lie_h_e (b := b) j i)
  have h : ⁅lowering P b i, ⁅raising P b i, raising P b j⁆⁆ = raising P b j := by
    rw [leibniz_lie, hFE, hFB, neg_lie, hHB]
    simp only [lie_zero, add_zero, neg_neg]
  simpa only [Ring.lie_def] using h

/-- The integral lowering-bracket identity survives every coefficient reduction. -/
theorem loweringOver_a2_bracket_eq_raising (R : Type*) [CommRing R]
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = -1) :
    loweringOver P b R i *
        (raisingOver P b R i * raisingOver P b R j -
          raisingOver P b R j * raisingOver P b R i) -
      (raisingOver P b R i * raisingOver P b R j -
          raisingOver P b R j * raisingOver P b R i) *
        loweringOver P b R i = raisingOver P b R j := by
  have h := congrArg (Int.castRingHom R).mapMatrix
    (lowering_a2_bracket_eq_raising P b hdiamond i j hne hji)
  simp only [map_sub, map_mul] at h
  simpa only [raisingOver, loweringOver, RingHom.mapMatrix_apply] using h

end Atlas.Chevalley.Integral
