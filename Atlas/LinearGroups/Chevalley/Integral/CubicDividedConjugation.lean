import Atlas.LinearGroups.Chevalley.Integral.GeckExponentialRational
import Mathlib.Tactic.Module

/-! The integral cubic conjugation coefficient of the actual Geck raising
exponential. The four terms make sense in every characteristic. Rational
normalization is used only for proving the integral identity later. -/

noncomputable section
namespace Atlas.Chevalley.Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- The explicit cubic coefficient in x_i(T) B x_i(-T), formed using the
already-constructed integral divided powers before any coefficient reduction.
No denominator is part of this definition. -/
def raisingConjugationCubic (i : b.support)
    (B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  raisingDividedOver P b R i 3 * B -
    raisingDividedOver P b R i 2 * B * raisingOver P b R i +
    raisingOver P b R i * B * raisingDividedOver P b R i 2 -
    B * raisingDividedOver P b R i 3

variable {R} {S : Type*} [CommRing S]

private theorem raisingDividedOver_map (φ : R →+* S) (i : b.support) (n : ℕ) :
    (raisingDividedOver P b R i n).map φ = raisingDividedOver P b S i n := by
  ext row col
  simp [raisingDividedOver]

/-- The explicit integral coefficient commutes with every scalar homomorphism. -/
theorem raisingConjugationCubic_map (φ : R →+* S) (i : b.support)
    (B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :
    (raisingConjugationCubic P b R i B).map φ =
      raisingConjugationCubic P b S i (B.map φ) := by
  simp only [raisingConjugationCubic, Matrix.map_sub φ (map_sub φ),
    Matrix.map_add φ (map_add φ), Matrix.map_mul,
    raisingDividedOver_map, raisingOver_map]

variable (R) [Algebra ℚ R]

private theorem raisingDividedOver_eq_inv_factorial (i : b.support) (n : ℕ) :
    raisingDividedOver P b R i n =
      (n.factorial : ℚ)⁻¹ • raisingOver P b R i ^ n := by
  have hfac : (n.factorial : ℚ) • raisingDividedOver P b R i n =
      raisingOver P b R i ^ n := by
    simpa only [Nat.cast_smul_eq_nsmul] using
      factorial_smul_raisingDividedOver P b R i n
  have hn : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [← hfac, inv_smul_smul₀ hn]

/-- Over rational coefficient algebras the explicit integral coefficient is
the triple bracket divided by six. This lemma is not used to divide after
reduction in characteristics two or three. -/
theorem raisingConjugationCubic_eq_sixth_bracket (i : b.support)
    (B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :
    let A := raisingOver P b R i
    let C := A * B - B * A
    let D := A * C - C * A
    raisingConjugationCubic P b R i B = (1 / 6 : ℚ) • (A * D - D * A) := by
  dsimp only
  have h2 : raisingDividedOver P b R i 2 =
      (1 / 2 : ℚ) • raisingOver P b R i ^ 2 := by
    simpa using raisingDividedOver_eq_inv_factorial P b R i 2
  have h3 : raisingDividedOver P b R i 3 =
      (1 / 6 : ℚ) • raisingOver P b R i ^ 3 := by
    simpa [show Nat.factorial 3 = 6 from rfl] using
      raisingDividedOver_eq_inv_factorial P b R i 3
  simp only [raisingConjugationCubic, h2, h3, pow_succ, pow_zero, mul_one, one_mul,
    mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub, mul_assoc]
  module

end Atlas.Chevalley.Integral
