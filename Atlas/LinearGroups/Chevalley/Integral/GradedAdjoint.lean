import Atlas.LinearGroups.Chevalley.Integral.GradedMatrix
import Atlas.LinearGroups.Chevalley.Integral.GeckExponential
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations

/-! Exact root-coroot degrees of integral Geck matrices and their divided powers.
The Lie relations are used over ℤ only; diagonal conjugation is then reduced
to arbitrary commutative rings. -/
noncomputable section
namespace Atlas.Chevalley.Integral
open RootPairing.GeckConstruction
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- The integer weight of each Cartan or root coordinate. -/
def geckWeight (i : b.support) : b.support ⊕ ι → ℤ :=
  Sum.elim (0 : b.support → ℤ) (fun j => P.pairingIn ℤ j i)

omit [P.IsReduced] in
theorem raising_weightedSupport (i j : b.support) :
    WeightedSupport (geckWeight P b i) (b.cartanMatrix j i) (raising P b j) := by
  apply WeightedSupport.of_diagonal_commutator
  simpa [h_eq_diagonal, geckWeight, raising, Ring.lie_def] using
    (lie_h_e (b := b) j i)

omit [P.IsReduced] in
theorem lowering_weightedSupport (i j : b.support) :
    WeightedSupport (geckWeight P b i) (-b.cartanMatrix j i) (lowering P b j) := by
  apply WeightedSupport.of_diagonal_commutator
  simpa [h_eq_diagonal, geckWeight, lowering, Ring.lie_def] using
    (lie_h_f (b := b) j i)

theorem raisingDividedPower_weightedSupport (i j : b.support) (n : ℕ) :
    WeightedSupport (geckWeight P b i) ((n : ℤ)*b.cartanMatrix j i)
      (raisingDividedPower P b j n) :=
  (raising_weightedSupport P b i j).divided n
    (factorial_smul_raisingDividedPower P b j n)

theorem loweringDividedPower_weightedSupport (i j : b.support) (n : ℕ) :
    WeightedSupport (geckWeight P b i) ((n : ℤ)*(-b.cartanMatrix j i))
      (loweringDividedPower P b j n) :=
  (lowering_weightedSupport P b i j).divided n
    (factorial_smul_loweringDividedPower P b j n)

variable (R : Type*) [CommRing R]

def geckWeightDiagonal (i : b.support) (t : Rˣ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  Matrix.diagonal (fun a => (t ^ geckWeight P b i a).val)

theorem geckWeightDiagonal_raisingDivided (i j : b.support) (n : ℕ) (t : Rˣ) :
    geckWeightDiagonal P b R i t * raisingDividedOver P b R j n =
      (t^((n : ℤ)*b.cartanMatrix j i)).val •
        (raisingDividedOver P b R j n * geckWeightDiagonal P b R i t) :=
  (raisingDividedPower_weightedSupport P b i j n).diagonal_mul_map R t

theorem geckWeightDiagonal_loweringDivided (i j : b.support) (n : ℕ) (t : Rˣ) :
    geckWeightDiagonal P b R i t *
        (loweringDividedPower P b j n).map (Int.castRingHom R) =
      (t^((n : ℤ)*(-b.cartanMatrix j i))).val •
        ((loweringDividedPower P b j n).map (Int.castRingHom R) *
          geckWeightDiagonal P b R i t) :=
  (loweringDividedPower_weightedSupport P b i j n).diagonal_mul_map R t

theorem unit_zpow_nat_mul_val (t : Rˣ) (n : ℕ) (d : ℤ) :
    (t^((n : ℤ)*d)).val = (t^d).val^n := by
  rw [mul_comm, zpow_mul, zpow_natCast, Units.val_pow_eq_pow_val]

/-- All-ring torus scaling of the actual raising exponential, with the
root/coroot orientation inherited from the actual integral Cartan matrix. -/
theorem geckWeightDiagonal_raisingExponential (i j : b.support) (t : Rˣ) (s : R) :
    geckWeightDiagonal P b R i t * raisingExponential P b R j s =
      raisingExponential P b R j ((t^b.cartanMatrix j i).val*s) *
        geckWeightDiagonal P b R i t := by
  rw [raisingExponential, raisingExponential, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Matrix.mul_smul, geckWeightDiagonal_raisingDivided, Matrix.smul_mul,
    smul_smul, unit_zpow_nat_mul_val]
  congr 1
  rw [mul_pow, mul_comm]

theorem geckWeightDiagonal_loweringExponential (i j : b.support) (t : Rˣ) (s : R) :
    geckWeightDiagonal P b R i t * loweringExponential P b R j s =
      loweringExponential P b R j ((t^(-b.cartanMatrix j i)).val*s) *
        geckWeightDiagonal P b R i t := by
  rw [loweringExponential, loweringExponential, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Matrix.mul_smul, geckWeightDiagonal_loweringDivided, Matrix.smul_mul,
    smul_smul, unit_zpow_nat_mul_val]
  congr 1
  rw [mul_pow, mul_comm]

end Atlas.Chevalley.Integral
