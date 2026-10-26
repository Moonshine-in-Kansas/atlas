import Atlas.LinearGroups.Chevalley.Integral.A2ExponentialRational
import Atlas.LinearGroups.Chevalley.Adjoint
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Int.CharZero

/-! Integral polynomial descent of the actual A2 commutator's dependence on
the product of its two parameters. No divided powers of a bracket are assumed. -/

noncomputable section

namespace Atlas.Chevalley.Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Coefficient transport of the actual four-factor root commutator. -/
theorem raisingExponential_commutator_map
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (i j : b.support) (s t : R) :
    φ.mapMatrix (raisingExponential P b R i s * raisingExponential P b R j t *
        raisingExponential P b R i (-s) * raisingExponential P b R j (-t)) =
      raisingExponential P b S i (φ s) * raisingExponential P b S j (φ t) *
        raisingExponential P b S i (-(φ s)) *
          raisingExponential P b S j (-(φ t)) := by
  simp only [map_mul]
  simp only [RingHom.mapMatrix_apply, Atlas.Chevalley.raisingExponential_map, map_neg]

variable (hdiamond : SimpleDiamondProducts P b)
include hdiamond

private theorem raisingExponential_a2_commutator_intPolynomial
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    let Z := MvPolynomial (Fin 2) ℤ
    let x : Z := MvPolynomial.X 0
    let y : Z := MvPolynomial.X 1
    raisingExponential P b Z i x * raisingExponential P b Z j y *
        raisingExponential P b Z i (-x) * raisingExponential P b Z j (-y) =
      raisingExponential P b Z i 1 * raisingExponential P b Z j (x*y) *
        raisingExponential P b Z i (-1) * raisingExponential P b Z j (-(x*y)) := by
  dsimp only
  let φ : MvPolynomial (Fin 2) ℤ →+* MvPolynomial (Fin 2) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  have hφ : Function.Injective φ :=
    MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  apply Matrix.map_injective hφ
  change φ.mapMatrix _ = φ.mapMatrix _
  rw [raisingExponential_commutator_map, raisingExponential_commutator_map]
  simp only [map_one, map_mul]
  dsimp only [φ]
  simp only [MvPolynomial.map_X]
  rw [raisingExponential_a2_commutator_eq_exp P b hdiamond
      (MvPolynomial (Fin 2) ℚ) i j hne hij hji,
    raisingExponential_a2_commutator_eq_exp P b hdiamond
      (MvPolynomial (Fin 2) ℚ) i j hne hij hji]
  rw [one_mul]

/-- The actual A2 root commutator depends only on the product s*t, uniformly
over every commutative coefficient ring, including characteristics two and three. -/
theorem raisingExponential_a2_commutator_depends_on_product
    (R : Type*) [CommRing R] (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1)
    (s t : R) :
    raisingExponential P b R i s * raisingExponential P b R j t *
        raisingExponential P b R i (-s) * raisingExponential P b R j (-t) =
      raisingExponential P b R i 1 * raisingExponential P b R j (s*t) *
        raisingExponential P b R i (-1) * raisingExponential P b R j (-(s*t)) := by
  let ev : MvPolynomial (Fin 2) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R)
      (fun k : Fin 2 => if k = 0 then s else t)
  have hzero : ev (MvPolynomial.X 0) = s := by simp [ev]
  have hone : ev (MvPolynomial.X 1) = t := by simp [ev]
  have hz :=
    raisingExponential_a2_commutator_intPolynomial P b hdiamond i j hne hij hji
  dsimp only at hz
  have h := congrArg ev.mapMatrix hz
  rw [raisingExponential_commutator_map, raisingExponential_commutator_map] at h
  simpa only [map_one, map_mul, hzero, hone] using h

end Atlas.Chevalley.Integral
