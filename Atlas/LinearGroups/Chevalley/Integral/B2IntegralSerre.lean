import Atlas.LinearGroups.Chevalley.Integral.A2IntegralSerre
import Mathlib.Tactic.Module

/-! UNCOMPILED source candidate. The actual integral double-edge operator
identities. No finite-field division or rank-two group relation is assumed. -/

noncomputable section
namespace Atlas.Chevalley.Integral

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)

include hdiamond

/-- The actual integral cubic Serre relation for Cartan row j, column i=-2. -/
theorem raising_b2_serre (i j : b.support) (hne : i ≠ j)
    (hji : b.cartanMatrix j i = -2) :
    ⁅raising P b i, ⁅raising P b i, ⁅raising P b i, raising P b j⁆⁆⁆ = 0 := by
  let triple := (RootPairing.GeckConstruction.isSl2Triple (P := P) (b := b) i).symm
  have primitive : triple.HasPrimitiveVectorWith (raising P b j) (2 : ℤ) := by
    refine ⟨(RootPairing.GeckConstruction.isSl2Triple (P := P) (b := b) j).e_ne_zero,
      ?_, ?_⟩
    · change ⁅-RootPairing.GeckConstruction.h i, RootPairing.GeckConstruction.e j⁆ =
        (2 : ℤ) • RootPairing.GeckConstruction.e j
      rw [neg_lie, RootPairing.GeckConstruction.lie_h_e, hji]
      module
    · change lowering P b i * raising P b j - raising P b j * lowering P b i = 0
      exact sub_eq_zero.mpr
        (raising_lowering_commute_of_diamond P b hdiamond j i hne.symm).symm.eq
  have hz := primitive.pow_toEnd_f_eq_zero_of_eq_nat (n := 2) (by rfl)
  change (LieModule.toEnd ℤ
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
      (raising P b i) ^ (3 : ℕ)) (raising P b j) = 0 at hz
  simpa only [pow_succ, pow_zero, Module.End.mul_apply,
    Module.End.one_apply, LieModule.toEnd_apply_apply] using hz

/-- The first lowering step on the actual double-edge string has coefficient two. -/
theorem lowering_b2_bracket_eq_two_raising (i j : b.support) (hne : i ≠ j)
    (hji : b.cartanMatrix j i = -2) :
    ⁅lowering P b i, ⁅raising P b i, raising P b j⁆⁆ = (2 : ℤ) • raising P b j := by
  have hFE : ⁅lowering P b i, raising P b i⁆ =
      -RootPairing.GeckConstruction.h i := by
    change ⁅RootPairing.GeckConstruction.f i, RootPairing.GeckConstruction.e i⁆ = _
    rw [← lie_skew, RootPairing.GeckConstruction.lie_e_f_same]
  have hFB : ⁅lowering P b i, raising P b j⁆ = 0 := by
    change lowering P b i * raising P b j - raising P b j * lowering P b i = 0
    exact sub_eq_zero.mpr
      (raising_lowering_commute_of_diamond P b hdiamond j i hne.symm).symm.eq
  have hHB : ⁅RootPairing.GeckConstruction.h i, raising P b j⁆ =
      (-2 : ℤ) • raising P b j := by
    simpa only [hji] using (RootPairing.GeckConstruction.lie_h_e (b := b) j i)
  rw [leibniz_lie, hFE, hFB, neg_lie, hHB, lie_zero, add_zero]
  module

/-- The second lowering step also has coefficient two; all identities are over Z. -/
theorem lowering_b2_double_bracket_eq_two_bracket
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = -2) :
    ⁅lowering P b i, ⁅raising P b i, ⁅raising P b i, raising P b j⁆⁆⁆ =
      (2 : ℤ) • ⁅raising P b i, raising P b j⁆ := by
  have hFE : ⁅lowering P b i, raising P b i⁆ =
      -RootPairing.GeckConstruction.h i := by
    change ⁅RootPairing.GeckConstruction.f i, RootPairing.GeckConstruction.e i⁆ = _
    rw [← lie_skew, RootPairing.GeckConstruction.lie_e_f_same]
  have hHA : ⁅RootPairing.GeckConstruction.h i, raising P b i⁆ =
      (2 : ℤ) • raising P b i := by
    simpa only [b.cartanMatrix_apply_same] using
      (RootPairing.GeckConstruction.lie_h_e (b := b) i i)
  have hHB : ⁅RootPairing.GeckConstruction.h i, raising P b j⁆ =
      (-2 : ℤ) • raising P b j := by
    simpa only [hji] using (RootPairing.GeckConstruction.lie_h_e (b := b) j i)
  have hHC : ⁅RootPairing.GeckConstruction.h i, ⁅raising P b i, raising P b j⁆⁆ = 0 := by
    rw [leibniz_lie, hHA, hHB, smul_lie, lie_smul]
    module
  rw [leibniz_lie, hFE, lowering_b2_bracket_eq_two_raising P b hdiamond i j hne hji,
    neg_lie, hHC, neg_zero, zero_add, lie_smul]

end Atlas.Chevalley.Integral
