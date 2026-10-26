import Atlas.LinearGroups.Chevalley.Adjoint
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations

/-! Opposite distinct simple-root commutation. The Geck specialization honestly
retains pinned mathlib's irreducibility hypothesis; cancellation is integral. -/
noncomputable section
namespace Atlas.Chevalley.Integral

/-- Genuine factorial-divided matrices inherit commutation over the integers. -/
theorem divided_matrices_commute {d : Type*} [Fintype d] [DecidableEq d]
    (A B D E : Matrix d d ℤ) (k l : ℕ) (h : Commute A B)
    (hD : (k.factorial : ℤ) • D = A ^ k)
    (hE : (l.factorial : ℤ) • E = B ^ l) : Commute D E := by
  change D*E = E*D
  apply smul_right_injective (M := Matrix d d ℤ)
    (show (k.factorial : ℤ) * (l.factorial : ℤ) ≠ 0 by
      exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero k)
        (by exact_mod_cast Nat.factorial_ne_zero l))
  dsimp only
  calc
    ((k.factorial : ℤ) * (l.factorial : ℤ)) • (D*E) =
        ((k.factorial : ℤ) • D) * ((l.factorial : ℤ) • E) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
    _ = A^k * B^l := by rw [hD, hE]
    _ = B^l * A^k := (h.pow_pow k l).eq
    _ = ((l.factorial : ℤ) • E) * ((k.factorial : ℤ) • D) := by rw [hD, hE]
    _ = ((k.factorial : ℤ) * (l.factorial : ℤ)) • (E*D) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  [P.IsIrreducible] (b : P.Base)

omit [DecidableEq ι] in
/-- The genuine Geck raising and opposite lowering operators commute when the
simple indices are distinct. -/
theorem raising_lowering_commute (i j : b.support) (hij : i ≠ j) :
    Commute (raising P b i) (lowering P b j) := by
  have h := RootPairing.GeckConstruction.lie_e_f_ne (b := b) hij
  simpa only [Commute, SemiconjBy, Ring.lie_def, sub_eq_zero] using h

theorem raising_lowering_divided_commute (i j : b.support) (hij : i ≠ j) (k l : ℕ) :
    Commute (raisingDividedPower P b i k) (loweringDividedPower P b j l) :=
  divided_matrices_commute (raising P b i) (lowering P b j) _ _ k l
    (raising_lowering_commute P b i j hij)
    (factorial_smul_raisingDividedPower P b i k)
    (factorial_smul_loweringDividedPower P b j l)

variable (R : Type*) [CommRing R]

theorem raising_lowering_dividedOver_commute (i j : b.support) (hij : i ≠ j) (k l : ℕ) :
    Commute (raisingDividedOver P b R i k)
      ((loweringDividedPower P b j l).map (Int.castRingHom R)) := by
  have h := congrArg (fun A => A.map (Int.castRingHom R))
    (raising_lowering_divided_commute P b i j hij k l).eq
  simpa only [Commute, SemiconjBy, Matrix.map_mul, raisingDividedOver] using h

/-- Every commutative coefficient ring is allowed, including characteristics
2 and 3; no factorial is cancelled in this ring. -/
theorem raising_lowering_exponential_commute (i j : b.support) (hij : i ≠ j) (s t : R) :
    Commute (raisingExponential P b R i s) (loweringExponential P b R j t) := by
  unfold raisingExponential loweringExponential
  apply Commute.sum_left
  intro k hk
  apply Commute.sum_right
  intro l hl
  exact ((raising_lowering_dividedOver_commute P b R i j hij k l).smul_left (s^k)).smul_right (t^l)

end Atlas.Chevalley.Integral
namespace Atlas.Chevalley
open Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  [P.IsIrreducible] (b : P.Base) (R : Type*) [CommRing R]

/-- Opposite root elements in the actual generated adjoint group commute for
distinct simple indices. -/
theorem adjointX_commute_adjointY (i j : b.support) (hij : i ≠ j) (s t : R) :
    Commute (adjointX P b R i s) (adjointY P b R j t) := by
  change adjointX P b R i s * adjointY P b R j t =
    adjointY P b R j t * adjointX P b R i s
  apply Subtype.ext
  apply Units.ext
  change raisingExponential P b R i s * (loweringRootElement P b R j t).val =
    (loweringRootElement P b R j t).val * raisingExponential P b R i s
  rw [loweringRootElement_val]
  exact (raising_lowering_exponential_commute P b R i j hij s t).eq

end Atlas.Chevalley
