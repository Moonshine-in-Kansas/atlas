import Atlas.LinearGroups.Chevalley.A2WeylRational
import Atlas.LinearGroups.Chevalley.Integral.A2CommutatorProduct
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Int.CharZero

/-! Integral polynomial descent of the actual pinned A2 commutator relation. -/

noncomputable section
namespace Atlas.Chevalley
open Integral
open scoped commutatorElement

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Coefficient maps preserve the actual pinned Weyl word at parameter one. -/
theorem adjointMap_weyl_one {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (i : b.support) :
    adjointMap P b φ (adjointWeyl P b R i 1) = adjointWeyl P b S i 1 := by
  change adjointMap P b φ
      (adjointX P b R i 1 * adjointY P b R i (-1) * adjointX P b R i 1) =
    adjointX P b S i 1 * adjointY P b S i (-1) * adjointX P b S i 1
  simp only [map_mul, adjointMap_x, adjointMap_y, map_one, map_neg]

variable (hdiamond : SimpleDiamondProducts P b)
include hdiamond

private theorem adjointX_a2_commutator_one_eq_weyl_conjugate_intPolynomial
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    let Z := MvPolynomial Unit ℤ
    let t : Z := MvPolynomial.X ()
    ⁅adjointX P b Z i 1, adjointX P b Z j t⁆ =
      adjointWeyl P b Z i 1 * adjointX P b Z j t * (adjointWeyl P b Z i 1)⁻¹ := by
  dsimp only
  let φ : MvPolynomial Unit ℤ →+* MvPolynomial Unit ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  have hφ : Function.Injective φ :=
    MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  apply adjointMap_injective P b φ hφ
  simpa only [map_commutatorElement, map_mul, map_inv, adjointMap_x,
    adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using
    adjointX_a2_commutator_one_eq_weyl_conjugate_rat
      P b hdiamond (MvPolynomial Unit ℚ) i j hne hij hji (MvPolynomial.X ())

/-- The commutator at (1,t) is the actual Weyl-conjugate root element over
every commutative ring, by descent of an integral polynomial word identity. -/
theorem adjointX_a2_commutator_one_eq_weyl_conjugate
    (R : Type*) [CommRing R] (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (t : R) :
    ⁅adjointX P b R i 1, adjointX P b R j t⁆ =
      adjointWeyl P b R i 1 * adjointX P b R j t * (adjointWeyl P b R i 1)⁻¹ := by
  let ev : MvPolynomial Unit ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) (fun _ => t)
  have hz := adjointX_a2_commutator_one_eq_weyl_conjugate_intPolynomial
    P b hdiamond i j hne hij hji
  dsimp only at hz
  have h := congrArg (adjointMap P b ev) hz
  simpa only [map_commutatorElement, map_mul, map_inv, adjointMap_x,
    adjointMap_weyl_one, map_one, ev, MvPolynomial.eval₂Hom_X'] using h

/-- The pinned A2 root commutator in the actual Adjoint group, uniformly
in every characteristic: [X_i(s),X_j(t)]=w_i X_j(st) w_i⁻¹. -/
theorem adjointX_a2_commutator_eq_weyl_conjugate
    (R : Type*) [CommRing R] (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (s t : R) :
    ⁅adjointX P b R i s, adjointX P b R j t⁆ =
      adjointWeyl P b R i 1 * adjointX P b R j (s*t) * (adjointWeyl P b R i 1)⁻¹ := by
  have hprod : ⁅adjointX P b R i s, adjointX P b R j t⁆ =
      ⁅adjointX P b R i 1, adjointX P b R j (s*t)⁆ := by
    apply Subtype.ext
    apply Units.ext
    exact raisingExponential_a2_commutator_depends_on_product
      P b hdiamond R i j hne hij hji s t
  exact hprod.trans
    (adjointX_a2_commutator_one_eq_weyl_conjugate P b hdiamond R i j hne hij hji (s*t))

end Atlas.Chevalley
