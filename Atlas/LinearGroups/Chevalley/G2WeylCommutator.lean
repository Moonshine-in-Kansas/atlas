import Atlas.LinearGroups.Chevalley.G2CommutatorRational
import Atlas.LinearGroups.Chevalley.A2WeylCommutator

/-! Integral polynomial descent of the four-factor short/long G2 commutator.
No rational-algebra or characteristic hypothesis remains in the public theorem.
This source candidate has not been checked by its author. -/

noncomputable section
namespace Atlas.Chevalley
open Integral
open scoped commutatorElement

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)

include hdiamond

private theorem adjointX_g2_commutator_eq_weyl_product_intPolynomial
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    let Z := MvPolynomial (Fin 2) ℤ
    let s : Z := MvPolynomial.X 0
    let t : Z := MvPolynomial.X 1
    ⁅adjointX P b Z i s, adjointX P b Z j t⁆ =
      (adjointWeyl P b Z j 1 * adjointX P b Z i (-s*t) *
        (adjointWeyl P b Z j 1)⁻¹) *
      ((adjointWeyl P b Z i 1 * adjointWeyl P b Z j 1) *
        adjointX P b Z i (s^2*t) * (adjointWeyl P b Z i 1 * adjointWeyl P b Z j 1)⁻¹) *
      (adjointWeyl P b Z i 1 * adjointX P b Z j (s^3*t) *
        (adjointWeyl P b Z i 1)⁻¹) *
      ((adjointWeyl P b Z j 1 * adjointWeyl P b Z i 1) *
        adjointX P b Z j (2*s^3*t^2) *
          (adjointWeyl P b Z j 1 * adjointWeyl P b Z i 1)⁻¹) := by
  dsimp only
  let φ : MvPolynomial (Fin 2) ℤ →+* MvPolynomial (Fin 2) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  have hφ : Function.Injective φ :=
    MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  apply adjointMap_injective P b φ hφ
  simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat,
    adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using
    adjointX_g2_commutator_eq_weyl_product_rat P b hdiamond
      (MvPolynomial (Fin 2) ℚ) i j hne hij hji (MvPolynomial.X 0) (MvPolynomial.X 1)

/-- The actual G2 simple-node commutator over every commutative ring.
For the literal Weyl words j, ij, i, ji, the factors occur in increasing
root height with parameters -st, s²t, s³t, 2s³t². -/
theorem adjointX_g2_commutator_eq_weyl_product
    (R : Type*) [CommRing R] (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3)
    (s t : R) :
    ⁅adjointX P b R i s, adjointX P b R j t⁆ =
      (adjointWeyl P b R j 1 * adjointX P b R i (-s*t) *
        (adjointWeyl P b R j 1)⁻¹) *
      ((adjointWeyl P b R i 1 * adjointWeyl P b R j 1) *
        adjointX P b R i (s^2*t) * (adjointWeyl P b R i 1 * adjointWeyl P b R j 1)⁻¹) *
      (adjointWeyl P b R i 1 * adjointX P b R j (s^3*t) *
        (adjointWeyl P b R i 1)⁻¹) *
      ((adjointWeyl P b R j 1 * adjointWeyl P b R i 1) *
        adjointX P b R j (2*s^3*t^2) *
          (adjointWeyl P b R j 1 * adjointWeyl P b R i 1)⁻¹) := by
  let ev : MvPolynomial (Fin 2) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R)
      (fun k : Fin 2 => if k = 0 then s else t)
  have hzero : ev (MvPolynomial.X 0) = s := by simp [ev]
  have hone : ev (MvPolynomial.X 1) = t := by simp [ev]
  have hz := adjointX_g2_commutator_eq_weyl_product_intPolynomial
    P b hdiamond i j hne hij hji
  dsimp only at hz
  have h := congrArg (adjointMap P b ev) hz
  simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat,
    adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using h

end Atlas.Chevalley
