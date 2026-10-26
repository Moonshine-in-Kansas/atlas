import Atlas.LinearGroups.Chevalley.Integral.A2IntegralSerre
import Atlas.LinearGroups.Chevalley.AdjointOpposition

/-! Source candidate: nonadjacent simple root groups commute over every
commutative coefficient ring, using integral divided powers before reduction. -/

noncomputable section
namespace Atlas.Chevalley.Integral
attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)

include hdiamond

/-- The actual Geck raising operators commute at a zero Cartan entry. -/
theorem raising_commute_of_zero_cartan (i j : b.support) (hne : i ≠ j)
    (hji : b.cartanMatrix j i = 0) :
    Commute (raising P b i) (raising P b j) := by
  let triple := (RootPairing.GeckConstruction.isSl2Triple (P := P) (b := b) i).symm
  have primitive : triple.HasPrimitiveVectorWith (raising P b j) (0 : ℤ) := by
    refine ⟨(RootPairing.GeckConstruction.isSl2Triple (P := P) (b := b) j).e_ne_zero,
      ?_, ?_⟩
    · change ⁅-RootPairing.GeckConstruction.h i, RootPairing.GeckConstruction.e j⁆ =
        (0 : ℤ) • RootPairing.GeckConstruction.e j
      rw [neg_lie, RootPairing.GeckConstruction.lie_h_e, hji]
      simp only [zero_smul, neg_zero]
    · change lowering P b i * raising P b j - raising P b j * lowering P b i = 0
      exact sub_eq_zero.mpr
        (raising_lowering_commute_of_diamond P b hdiamond j i hne.symm).symm.eq
  have hz := primitive.pow_toEnd_f_eq_zero_of_eq_nat (n := 0) (by rfl)
  change (LieModule.toEnd ℤ
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
      (raising P b i) ^ (1 : ℕ)) (raising P b j) = 0 at hz
  simpa only [pow_one, LieModule.toEnd_apply_apply, Ring.lie_def,
    sub_eq_zero, Commute, SemiconjBy] using hz

/-- Commuting integral raising operators have commuting integral divided powers. -/
theorem raising_divided_commute_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0) (k l : ℕ) :
    Commute (raisingDividedPower P b i k) (raisingDividedPower P b j l) :=
  divided_matrices_commute (raising P b i) (raising P b j) _ _ k l
    (raising_commute_of_zero_cartan P b hdiamond i j hne hji)
    (factorial_smul_raisingDividedPower P b i k)
    (factorial_smul_raisingDividedPower P b j l)

variable (R : Type*) [CommRing R]

/-- Reduction to any characteristic preserves the integral divided-power identity. -/
theorem raising_dividedOver_commute_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0) (k l : ℕ) :
    Commute (raisingDividedOver P b R i k) (raisingDividedOver P b R j l) := by
  have h := congrArg (fun A => A.map (Int.castRingHom R))
    (raising_divided_commute_of_zero_cartan P b hdiamond i j hne hji k l).eq
  simpa only [Commute, SemiconjBy, Matrix.map_mul, raisingDividedOver] using h

/-- The actual integral exponentials commute, with no denominator in the target ring. -/
theorem raising_exponential_commute_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0) (s t : R) :
    Commute (raisingExponential P b R i s) (raisingExponential P b R j t) := by
  unfold raisingExponential
  apply Commute.sum_left
  intro k hk
  apply Commute.sum_right
  intro l hl
  exact ((raising_dividedOver_commute_of_zero_cartan P b hdiamond R i j hne hji k l).smul_left (s ^ k)).smul_right (t ^ l)

end Atlas.Chevalley.Integral

namespace Atlas.Chevalley
open Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b) (R : Type*) [CommRing R]

include hdiamond

/-- Actual positive simple-root subgroups commute at a zero Cartan entry. -/
theorem adjointX_commute_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0) (s t : R) :
    Commute (adjointX P b R i s) (adjointX P b R j t) := by
  change adjointX P b R i s * adjointX P b R j t =
    adjointX P b R j t * adjointX P b R i s
  apply Subtype.ext
  apply Units.ext
  exact (raising_exponential_commute_of_zero_cartan P b hdiamond R i j hne hji s t).eq

/-- The actual opposition automorphism supplies the negative-root identity. -/
theorem adjointY_commute_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0) (s t : R) :
    Commute (adjointY P b R i s) (adjointY P b R j t) := by
  have h := congrArg (adjointOppositionEquiv P b R)
    (adjointX_commute_of_zero_cartan P b hdiamond R i j hne hji s t).eq
  simpa only [map_mul, adjointOppositionEquiv_X, Commute, SemiconjBy] using h

end Atlas.Chevalley
