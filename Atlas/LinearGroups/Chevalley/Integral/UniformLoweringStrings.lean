import Atlas.LinearGroups.Chevalley.Integral.UniformIntegralSerre

/-! Lowering coefficients on actual integral simple-root operator strings.
This uses the pinned sl2 primitive-vector formula, including the triple edge. -/

noncomputable section
namespace Atlas.Chevalley.Integral
attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)

include hdiamond

/-- The coefficient is (k+1)(n−k) in Z, without truncating subtraction in N. -/
theorem lowering_iterated_raising_of_cartan_eq_neg_nat
    (i j : b.support) (hne : i ≠ j) (n : ℕ)
    (hji : b.cartanMatrix j i = -(n : ℤ)) (k : ℕ) :
    ⁅lowering P b i,
      (LieModule.toEnd ℤ
        (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
        (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
        (raising P b i) ^ (k + 1)) (raising P b j)⁆ =
      (((k : ℤ) + 1) * ((n : ℤ) - (k : ℤ))) •
        (LieModule.toEnd ℤ
          (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
          (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
          (raising P b i) ^ k) (raising P b j) := by
  let triple := (RootPairing.GeckConstruction.isSl2Triple (P := P) (b := b) i).symm
  have primitive : triple.HasPrimitiveVectorWith (raising P b j) (n : ℤ) := by
    refine ⟨(RootPairing.GeckConstruction.isSl2Triple (P := P) (b := b) j).e_ne_zero,
      ?_, ?_⟩
    · change ⁅-RootPairing.GeckConstruction.h i, RootPairing.GeckConstruction.e j⁆ =
        (n : ℤ) • RootPairing.GeckConstruction.e j
      rw [neg_lie, RootPairing.GeckConstruction.lie_h_e, hji]
      simp only [neg_smul, neg_neg]
    · change lowering P b i * raising P b j - raising P b j * lowering P b i = 0
      exact sub_eq_zero.mpr
        (raising_lowering_commute_of_diamond P b hdiamond j i hne.symm).symm.eq
  exact primitive.lie_e_pow_succ_toEnd_f k

/-- Exact integral coefficients 3,4,3 for the actual triple-edge string. -/
theorem lowering_g2_operator_string
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = -3) :
    ⁅lowering P b i, ⁅raising P b i, raising P b j⁆⁆ =
        (3 : ℤ) • raising P b j ∧
      ⁅lowering P b i, ⁅raising P b i, ⁅raising P b i, raising P b j⁆⁆⁆ =
        (4 : ℤ) • ⁅raising P b i, raising P b j⁆ ∧
      ⁅lowering P b i,
          ⁅raising P b i, ⁅raising P b i, ⁅raising P b i, raising P b j⁆⁆⁆⁆ =
        (3 : ℤ) • ⁅raising P b i, ⁅raising P b i, raising P b j⁆⁆ := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [pow_succ, pow_zero, Module.End.mul_apply, Module.End.one_apply,
      LieModule.toEnd_apply_apply, Nat.cast_zero, Nat.cast_ofNat, zero_add, sub_zero, one_mul] using
      lowering_iterated_raising_of_cartan_eq_neg_nat P b hdiamond i j hne 3 hji 0
  · simpa only [pow_succ, pow_zero, Module.End.mul_apply, Module.End.one_apply,
      LieModule.toEnd_apply_apply, Nat.cast_one, Nat.cast_ofNat,
      show ((1 : ℤ) + 1) * (3 - 1) = 4 by norm_num] using
      lowering_iterated_raising_of_cartan_eq_neg_nat P b hdiamond i j hne 3 hji 1
  · simpa only [pow_succ, pow_zero, Module.End.mul_apply, Module.End.one_apply,
      LieModule.toEnd_apply_apply, Nat.cast_ofNat,
      show ((2 : ℤ) + 1) * (3 - 2) = 3 by norm_num] using
      lowering_iterated_raising_of_cartan_eq_neg_nat P b hdiamond i j hne 3 hji 2

end Atlas.Chevalley.Integral
