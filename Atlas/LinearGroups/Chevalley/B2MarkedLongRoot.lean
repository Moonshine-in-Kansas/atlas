import Atlas.LinearGroups.Chevalley.B2MarkedLongRootRational
import Atlas.LinearGroups.Chevalley.A2WeylCommutator

/-! Integral polynomial descent of the marked long-root B2 identity.
Division by two occurs only in the preceding rational calculation. -/
noncomputable section
namespace Atlas.Chevalley
open Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)

include hdiamond

private theorem adjointWeyl_b2_fixes_long_conjugate_X_intPolynomial
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    let Z := MvPolynomial (Fin 1) ℤ
    let t : Z := MvPolynomial.X 0
    adjointWeyl P b Z j 1 *
        (adjointWeyl P b Z i 1 * adjointX P b Z j t * (adjointWeyl P b Z i 1)⁻¹) *
        (adjointWeyl P b Z j 1)⁻¹ =
      adjointWeyl P b Z i 1 * adjointX P b Z j t * (adjointWeyl P b Z i 1)⁻¹ := by
  dsimp only
  let φ : MvPolynomial (Fin 1) ℤ →+* MvPolynomial (Fin 1) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  have hφ : Function.Injective φ :=
    MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  apply adjointMap_injective P b φ hφ
  simpa only [map_mul, map_inv, adjointMap_x, adjointMap_weyl_one,
    map_one, φ, MvPolynomial.map_X] using
    adjointWeyl_b2_fixes_long_conjugate_X_rat P b hdiamond
      (MvPolynomial (Fin 1) ℚ) i j hne hij hji (MvPolynomial.X 0)

/-- Over every commutative ring, the long simple Weyl element fixes the
actual long-root family conjugated by the short simple Weyl element. -/
theorem adjointWeyl_b2_fixes_long_conjugate_X
    (R : Type*) [CommRing R] (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) (t : R) :
    adjointWeyl P b R j 1 *
        (adjointWeyl P b R i 1 * adjointX P b R j t * (adjointWeyl P b R i 1)⁻¹) *
        (adjointWeyl P b R j 1)⁻¹ =
      adjointWeyl P b R i 1 * adjointX P b R j t * (adjointWeyl P b R i 1)⁻¹ := by
  let ev : MvPolynomial (Fin 1) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) (fun _ => t)
  have hzero : ev (MvPolynomial.X 0) = t := by simp [ev]
  have hz := adjointWeyl_b2_fixes_long_conjugate_X_intPolynomial P b hdiamond i j hne hij hji
  dsimp only at hz
  have h := congrArg (adjointMap P b ev) hz
  simpa only [map_mul, map_inv, adjointMap_x, adjointMap_weyl_one, map_one, hzero] using h

end Atlas.Chevalley
