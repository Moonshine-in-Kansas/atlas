import Atlas.LinearGroups.Chevalley.Integral.GeckExponential
import Mathlib.RingTheory.Nilpotent.Exp

/-! Rational comparison for the existing integral Geck exponential.
The integral divided-power definition remains the all-characteristic model. -/

noncomputable section

namespace Atlas.Chevalley.Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- Factorial multiplication commutes with reduction of the integral divided powers. -/
theorem factorial_smul_raisingDividedOver (i : b.support) (n : ℕ) :
    (n.factorial : R) • raisingDividedOver P b R i n =
      raisingOver P b R i ^ n := by
  change _ = ((Int.castRingHom R).mapMatrix (raising P b i)) ^ n
  rw [← map_pow, ← factorial_smul_raisingDividedPower P b i n]
  ext row col
  simp only [raisingDividedOver, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast]

/-- The uniform degree-four bound survives coefficient reduction. -/
theorem raisingOver_four_eq_zero (i : b.support) :
    raisingOver P b R i ^ 4 = 0 := by
  change ((Int.castRingHom R).mapMatrix (raising P b i)) ^ 4 = 0
  rw [← map_pow, raising_four_eq_zero P b i, map_zero]

/-- Over a rational algebra, the integral root exponential agrees with the
algebraic exponential of its actual raising operator. -/
theorem raisingExponential_eq_nilpotent_exp [Algebra ℚ R]
    (i : b.support) (t : R) :
    raisingExponential P b R i t =
      IsNilpotent.exp (t • raisingOver P b R i) := by
  have hfour : (t • raisingOver P b R i) ^ 4 = 0 := by
    rw [smul_pow, raisingOver_four_eq_zero P b R i, smul_zero]
  rw [raisingExponential, IsNilpotent.exp_eq_sum hfour]
  apply Finset.sum_congr rfl
  intro n _
  have hfac : (n.factorial : ℚ) • raisingDividedOver P b R i n =
      raisingOver P b R i ^ n := by
    simpa only [Nat.cast_smul_eq_nsmul] using
      factorial_smul_raisingDividedOver P b R i n
  have hne : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  calc
    t ^ n • raisingDividedOver P b R i n =
        t ^ n • ((n.factorial : ℚ)⁻¹ • raisingOver P b R i ^ n) := by
      rw [← hfac, inv_smul_smul₀ hne]
    _ = (n.factorial : ℚ)⁻¹ • (t ^ n • raisingOver P b R i ^ n) :=
      smul_comm _ _ _
    _ = (n.factorial : ℚ)⁻¹ • (t • raisingOver P b R i) ^ n := by
      rw [smul_pow]

end Atlas.Chevalley.Integral
