import Atlas.LinearGroups.Chevalley.Integral.GeckExponential
import Atlas.LinearGroups.Chevalley.Adjoint

/-! Transfer of an integral scaled root-operator intertwining to all divided
powers and all root parameters. The operator intertwining is an explicit
premise, not inferred merely from the signed action on root basis vectors.
All cancellation takes place over the integers, before coefficient reduction. -/

noncomputable section
namespace Atlas.Chevalley.Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Integral factorial cancellation upgrades a scaled operator intertwining
to every divided power. No invertibility of the intertwiner is needed. -/
theorem raisingDividedPower_scaled_intertwining
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
    (i j : b.support) (σ : ℤ)
    (h : A * raising P b i = σ • (raising P b j * A)) (n : ℕ) :
    A * raisingDividedPower P b i n =
      σ ^ n • (raisingDividedPower P b j n * A) := by
  have hs : SemiconjBy A (raising P b i) (σ • raising P b j) := by
    simpa only [SemiconjBy, smul_mul_assoc] using h
  have hp : A * raising P b i ^ n = σ ^ n • (raising P b j ^ n * A) := by
    simpa only [SemiconjBy, smul_pow, smul_mul_assoc] using hs.pow_right n
  have hfac : (n.factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply (smul_right_injective
    (M := Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) hfac)
  calc
    (n.factorial : ℤ) • (A * raisingDividedPower P b i n) =
        A * ((n.factorial : ℤ) • raisingDividedPower P b i n) :=
      (mul_smul_comm _ _ _).symm
    _ = A * raising P b i ^ n := by rw [factorial_smul_raisingDividedPower]
    _ = σ ^ n • (raising P b j ^ n * A) := hp
    _ = σ ^ n • (((n.factorial : ℤ) • raisingDividedPower P b j n) * A) := by
      rw [factorial_smul_raisingDividedPower]
    _ = (n.factorial : ℤ) • (σ ^ n • (raisingDividedPower P b j n * A)) := by
      rw [smul_mul_assoc, smul_comm]

/-- Reduction of the already established integral equality retains every
divided-power coefficient in characteristic two and three. -/
theorem raisingDividedOver_scaled_intertwining
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
    (i j : b.support) (σ : ℤ)
    (h : A * raising P b i = σ • (raising P b j * A))
    (R : Type*) [CommRing R] (n : ℕ) :
    A.map (Int.castRingHom R) * raisingDividedOver P b R i n =
      (σ : R) ^ n • (raisingDividedOver P b R j n * A.map (Int.castRingHom R)) := by
  have hs (z : ℤ) (B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
      (z • B).map (Int.castRingHom R) = (z : R) • B.map (Int.castRingHom R) := by
    ext row col
    change ((z • B row col : ℤ) : R) = (z : R) • (B row col : R)
    simp only [zsmul_eq_mul, smul_eq_mul, Int.cast_mul]
  have hm := congrArg (fun B => B.map (Int.castRingHom R))
    (raisingDividedPower_scaled_intertwining P b A i j σ h n)
  simpa only [Matrix.map_mul, hs, Int.cast_pow, raisingDividedOver] using hm

/-- The complete, concretely defined root exponential inherits the scaled
intertwining over an arbitrary commutative coefficient ring. -/
theorem raisingExponential_scaled_intertwining
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
    (i j : b.support) (σ : ℤ)
    (h : A * raising P b i = σ • (raising P b j * A))
    (R : Type*) [CommRing R] (t : R) :
    A.map (Int.castRingHom R) * raisingExponential P b R i t =
      raisingExponential P b R j ((σ : R) * t) * A.map (Int.castRingHom R) := by
  unfold raisingExponential
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [raisingDividedOver_scaled_intertwining P b A i j σ h R n]
  rw [smul_smul, mul_pow]
  congr 1
  exact mul_comm _ _

end Atlas.Chevalley.Integral

namespace Atlas.Chevalley
open Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- The same integral implication expressed inside the actual adjoint group,
using its existing coefficient-reduction homomorphism. -/
theorem adjointMap_mul_X_of_integral_operator
    (g : Adjoint P b ℤ) (i j : b.support) (σ : ℤ)
    (h : g.val.val * raising P b i = σ • (raising P b j * g.val.val))
    (R : Type*) [CommRing R] (t : R) :
    adjointMap P b (Int.castRingHom R) g * adjointX P b R i t =
      adjointX P b R j ((σ : R) * t) * adjointMap P b (Int.castRingHom R) g := by
  apply Subtype.ext
  apply Units.ext
  exact raisingExponential_scaled_intertwining P b g.val.val i j σ h R t

/-- Conditional actual root-family conjugation. The still-needed mathematical
input is the integral operator identity, not only a root-label equality. -/
theorem adjointMap_conjugate_X_of_integral_operator
    (g : Adjoint P b ℤ) (i j : b.support) (σ : ℤ)
    (h : g.val.val * raising P b i = σ • (raising P b j * g.val.val))
    (R : Type*) [CommRing R] (t : R) :
    adjointMap P b (Int.castRingHom R) g * adjointX P b R i t *
      (adjointMap P b (Int.castRingHom R) g)⁻¹ =
        adjointX P b R j ((σ : R) * t) := by
  rw [adjointMap_mul_X_of_integral_operator P b g i j σ h R t]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

end Atlas.Chevalley
