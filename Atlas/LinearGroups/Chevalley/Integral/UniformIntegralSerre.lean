import Atlas.LinearGroups.Chevalley.Integral.A2IntegralSerre

/-! Source candidate: all integral simple-root Serre exponents are consequences
of the actual Geck sl2 triples. This includes the triple edge, without a
non-G2 assumption or reduction to finite-field examples. -/

noncomputable section
namespace Atlas.Chevalley.Integral
attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)

include hdiamond

/-- The actual raising operators satisfy (ad E_i)^(n+1)(E_j)=0 when
Cartan(j,i)=-n. The displayed exponent is uniform; the operators are integral. -/
theorem raising_serre_of_cartan_eq_neg_nat
    (i j : b.support) (hne : i ≠ j) (n : ℕ)
    (hji : b.cartanMatrix j i = -(n : ℤ)) :
    (LieModule.toEnd ℤ
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
      (raising P b i) ^ (n + 1)) (raising P b j) = 0 := by
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
  exact primitive.pow_toEnd_f_eq_zero_of_eq_nat (n := n) (by rfl)

/-- The actual integral triple-edge Serre identity, prior to coefficient reduction. -/
theorem raising_g2_serre
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = -3) :
    ⁅raising P b i, ⁅raising P b i, ⁅raising P b i, ⁅raising P b i, raising P b j⁆⁆⁆⁆ = 0 := by
  have hz := raising_serre_of_cartan_eq_neg_nat P b hdiamond i j hne 3 hji
  simpa only [pow_succ, pow_zero, Module.End.mul_apply,
    Module.End.one_apply, LieModule.toEnd_apply_apply] using hz

end Atlas.Chevalley.Integral
