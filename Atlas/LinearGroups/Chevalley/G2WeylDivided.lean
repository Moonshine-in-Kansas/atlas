import Atlas.LinearGroups.Chevalley.G2WeylRational
import Atlas.LinearGroups.Chevalley.A2WeylCommutator
import Atlas.LinearGroups.Chevalley.Integral.CubicDividedConjugation

/-! Actual all-characteristic triple-edge Weyl pinning. Equality of two
integer matrices is proved using the injective map Z -> Q. Only then is
the integer equality reduced to any target commutative ring. -/

noncomputable section
namespace Atlas.Chevalley
open Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

private theorem weylConjugateRaising_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (i j : b.support) :
    ((adjointWeyl P b R i 1).val.val * raisingOver P b R j *
      ((adjointWeyl P b R i 1)⁻¹).val.val).map φ =
      (adjointWeyl P b S i 1).val.val * raisingOver P b S j *
        ((adjointWeyl P b S i 1)⁻¹).val.val := by
  have hw : (adjointWeyl P b R i 1).val.val.map φ =
      (adjointWeyl P b S i 1).val.val :=
    congrArg (fun g : Adjoint P b S => g.val.val) (adjointMap_weyl_one P b φ i)
  have hi : ((adjointWeyl P b R i 1)⁻¹).val.val.map φ =
      ((adjointWeyl P b S i 1)⁻¹).val.val := by
    have h : adjointMap P b φ ((adjointWeyl P b R i 1)⁻¹) =
        (adjointWeyl P b S i 1)⁻¹ := by
      rw [map_inv, adjointMap_weyl_one]
    exact congrArg (fun g : Adjoint P b S => g.val.val) h
  rw [Matrix.map_mul, Matrix.map_mul, hw, hi, raisingOver_map]

variable (hdiamond : SimpleDiamondProducts P b)
include hdiamond

private theorem adjointWeyl_one_conjugate_raisingOver_g2_divided_int
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = -3) :
    (adjointWeyl P b ℤ i 1).val.val * raisingOver P b ℤ j *
      ((adjointWeyl P b ℤ i 1)⁻¹).val.val =
        raisingConjugationCubic P b ℤ i (raisingOver P b ℤ j) := by
  let φ : ℤ →+* ℚ := Int.castRingHom ℚ
  apply Matrix.map_injective (f := φ) (show Function.Injective φ from Int.cast_injective)
  dsimp only
  rw [weylConjugateRaising_map, raisingConjugationCubic_map, raisingOver_map]
  rw [raisingConjugationCubic_eq_sixth_bracket]
  exact adjointWeyl_one_conjugate_raisingOver_g2 P b hdiamond ℚ i j hne hji

/-- The actual pinned Weyl word sends E_j to the explicit integral cubic
divided-power expression. Unlike the six-times bracket identity, this
determines the conjugate in characteristics two and three as well. -/
theorem adjointWeyl_one_conjugate_raisingOver_g2_divided
    (R : Type*) [CommRing R] (i j : b.support) (hne : i ≠ j)
    (hji : b.cartanMatrix j i = -3) :
    (adjointWeyl P b R i 1).val.val * raisingOver P b R j *
      ((adjointWeyl P b R i 1)⁻¹).val.val =
        raisingConjugationCubic P b R i (raisingOver P b R j) := by
  have h := congrArg (fun A => A.map (Int.castRingHom R))
    (adjointWeyl_one_conjugate_raisingOver_g2_divided_int P b hdiamond i j hne hji)
  simpa only [weylConjugateRaising_map, raisingConjugationCubic_map,
    raisingOver_map] using h

end Atlas.Chevalley
