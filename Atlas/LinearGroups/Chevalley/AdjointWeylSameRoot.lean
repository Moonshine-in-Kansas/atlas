import Atlas.LinearGroups.Chevalley.AdjointWeylSameRootRational
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Int.CharZero

/-! The literal same-root Weyl identity over every commutative ring.
The integral polynomial identity is proved by injection into its rational
coefficient ring, then evaluated. No characteristic-two cancellation occurs. -/
noncomputable section
namespace Atlas.Chevalley
open Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

private theorem adjointWeyl_one_conjugate_Y_same_intPolynomial (i : b.support) :
    let Z := MvPolynomial (Fin 1) ℤ
    let t : Z := MvPolynomial.X 0
    adjointWeyl P b Z i 1 * adjointY P b Z i t *
      (adjointWeyl P b Z i 1)⁻¹ = adjointX P b Z i (-t) := by
  dsimp only
  let φ : MvPolynomial (Fin 1) ℤ →+* MvPolynomial (Fin 1) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  have hφ : Function.Injective φ :=
    MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  apply adjointMap_injective P b φ hφ
  simpa only [adjointWeyl, map_mul, map_inv, adjointMap_x, adjointMap_y,
    map_one, map_neg, Units.inv_eq_val_inv, inv_one, Units.val_one,
    φ, MvPolynomial.map_X] using
    adjointWeyl_one_conjugate_Y_same_rat P b (MvPolynomial (Fin 1) ℚ)
      i (MvPolynomial.X 0)

/-- The actual Weyl word n_i(1) takes Y_i(t) to X_i(-t) in every characteristic. -/
theorem adjointWeyl_one_conjugate_Y_same (R : Type*) [CommRing R]
    (i : b.support) (t : R) :
    adjointWeyl P b R i 1 * adjointY P b R i t *
      (adjointWeyl P b R i 1)⁻¹ = adjointX P b R i (-t) := by
  let ev : MvPolynomial (Fin 1) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) (fun _ => t)
  have hzero : ev (MvPolynomial.X 0) = t := by simp [ev]
  have hz := adjointWeyl_one_conjugate_Y_same_intPolynomial P b i
  dsimp only at hz
  have h := congrArg (adjointMap P b ev) hz
  simpa only [adjointWeyl, map_mul, map_inv, adjointMap_x, adjointMap_y,
    map_one, map_neg, Units.inv_eq_val_inv, inv_one, Units.val_one, hzero] using h

end Atlas.Chevalley
