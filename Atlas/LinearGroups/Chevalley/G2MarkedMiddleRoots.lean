import Atlas.LinearGroups.Chevalley.G2MarkedMiddleOperatorsRational
import Atlas.LinearGroups.Chevalley.IntegralRootOperatorTransfer
import Atlas.LinearGroups.Chevalley.A2WeylCommutator
import Mathlib.Tactic.Group

/-! The two actual marked middle-root identities over every commutative ring.
Integer operator equalities are descended from Q, then the existing factorial
intertwining theorem transfers every divided power before coefficient reduction. -/

noncomputable section
namespace Atlas.Chevalley
open Integral

private theorem unit_intertwining_of_fixed_conjugate
    {S : Type*} [Monoid S] (u v : Sˣ) (A : S)
    (h : u.val * (v.val * A * (v⁻¹).val) * (u⁻¹).val =
      v.val * A * (v⁻¹).val) :
    (v⁻¹ * u * v).val * A = A * (v⁻¹ * u * v).val := by
  have h' := congrArg (fun x => (v⁻¹).val * x * u.val * v.val) h
  simpa only [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left,
    Units.inv_mul, mul_one] using h'

private theorem group_fixed_conjugate_of_intertwining
    {G : Type*} [Group G] (u v x : G)
    (h : (v⁻¹ * u * v) * x = x * (v⁻¹ * u * v)) :
    u * (v * x * v⁻¹) * u⁻¹ = v * x * v⁻¹ := by
  calc
    _ = v * ((v⁻¹ * u * v) * x) * v⁻¹ * u⁻¹ := by group
    _ = v * (x * (v⁻¹ * u * v)) * v⁻¹ * u⁻¹ := by rw [h]
    _ = _ := by group

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

private theorem integral_intertwining_of_rational
    (g : Adjoint P b ℤ) (i : b.support)
    (h : (adjointMap P b (Int.castRingHom ℚ) g).val.val * raisingOver P b ℚ i =
      raisingOver P b ℚ i * (adjointMap P b (Int.castRingHom ℚ) g).val.val) :
    g.val.val * raising P b i = raising P b i * g.val.val := by
  apply Matrix.map_injective (f := Int.castRingHom ℚ)
    (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)
  dsimp only
  rw [Matrix.map_mul, Matrix.map_mul]
  exact h

variable (hdiamond : SimpleDiamondProducts P b)
include hdiamond

/-- The long simple Weyl element fixes the middle short-root family
represented by n_i n_j. This is valid in characteristics two and three too. -/
theorem adjointWeyl_g2_fixes_short_middle_X
    (R : Type*) [CommRing R] (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) (t : R) :
    adjointWeyl P b R j 1 *
      ((adjointWeyl P b R i 1 * adjointWeyl P b R j 1) * adjointX P b R i t *
        (adjointWeyl P b R i 1 * adjointWeyl P b R j 1)⁻¹) *
      (adjointWeyl P b R j 1)⁻¹ =
      (adjointWeyl P b R i 1 * adjointWeyl P b R j 1) * adjointX P b R i t *
        (adjointWeyl P b R i 1 * adjointWeyl P b R j 1)⁻¹ := by
  let g : Adjoint P b ℤ :=
    (adjointWeyl P b ℤ i 1 * adjointWeyl P b ℤ j 1)⁻¹ * adjointWeyl P b ℤ j 1 *
      (adjointWeyl P b ℤ i 1 * adjointWeyl P b ℤ j 1)
  have hQ := unit_intertwining_of_fixed_conjugate
    (adjointWeyl P b ℚ j 1).val
    (adjointWeyl P b ℚ i 1 * adjointWeyl P b ℚ j 1).val
    (raisingOver P b ℚ i)
    (adjointWeyl_g2_fixes_short_middle_operator_rat P b hdiamond ℚ i j hne hij hji)
  have hgQ :
      adjointMap P b (Int.castRingHom ℚ) g =
      (adjointWeyl P b ℚ i 1 * adjointWeyl P b ℚ j 1)⁻¹ * adjointWeyl P b ℚ j 1 *
        (adjointWeyl P b ℚ i 1 * adjointWeyl P b ℚ j 1) := by
    simp only [g, map_mul, map_inv, adjointMap_weyl_one]
  have hgR :
      adjointMap P b (Int.castRingHom R) g =
      (adjointWeyl P b R i 1 * adjointWeyl P b R j 1)⁻¹ * adjointWeyl P b R j 1 *
        (adjointWeyl P b R i 1 * adjointWeyl P b R j 1) := by
    simp only [g, map_mul, map_inv, adjointMap_weyl_one]
  have hint : g.val.val * raising P b i = raising P b i * g.val.val := by
    apply integral_intertwining_of_rational P b g i
    rw [hgQ]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hQ
  have h := adjointMap_mul_X_of_integral_operator P b g i i 1
    (by simpa only [one_smul] using hint) R t
  rw [hgR] at h
  simp only [Int.cast_one, one_mul] at h
  exact group_fixed_conjugate_of_intertwining
    (adjointWeyl P b R j 1)
    (adjointWeyl P b R i 1 * adjointWeyl P b R j 1)
    (adjointX P b R i t) h

/-- The short simple Weyl element fixes the middle long-root family
represented by n_j n_i. No denominator survives into this statement. -/
theorem adjointWeyl_g2_fixes_long_middle_X
    (R : Type*) [CommRing R] (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) (t : R) :
    adjointWeyl P b R i 1 *
      ((adjointWeyl P b R j 1 * adjointWeyl P b R i 1) * adjointX P b R j t *
        (adjointWeyl P b R j 1 * adjointWeyl P b R i 1)⁻¹) *
      (adjointWeyl P b R i 1)⁻¹ =
      (adjointWeyl P b R j 1 * adjointWeyl P b R i 1) * adjointX P b R j t *
        (adjointWeyl P b R j 1 * adjointWeyl P b R i 1)⁻¹ := by
  let g : Adjoint P b ℤ :=
    (adjointWeyl P b ℤ j 1 * adjointWeyl P b ℤ i 1)⁻¹ * adjointWeyl P b ℤ i 1 *
      (adjointWeyl P b ℤ j 1 * adjointWeyl P b ℤ i 1)
  have hQ := unit_intertwining_of_fixed_conjugate
    (adjointWeyl P b ℚ i 1).val
    (adjointWeyl P b ℚ j 1 * adjointWeyl P b ℚ i 1).val
    (raisingOver P b ℚ j)
    (adjointWeyl_g2_fixes_long_middle_operator_rat P b hdiamond ℚ i j hne hij hji)
  have hgQ :
      adjointMap P b (Int.castRingHom ℚ) g =
      (adjointWeyl P b ℚ j 1 * adjointWeyl P b ℚ i 1)⁻¹ * adjointWeyl P b ℚ i 1 *
        (adjointWeyl P b ℚ j 1 * adjointWeyl P b ℚ i 1) := by
    simp only [g, map_mul, map_inv, adjointMap_weyl_one]
  have hgR :
      adjointMap P b (Int.castRingHom R) g =
      (adjointWeyl P b R j 1 * adjointWeyl P b R i 1)⁻¹ * adjointWeyl P b R i 1 *
        (adjointWeyl P b R j 1 * adjointWeyl P b R i 1) := by
    simp only [g, map_mul, map_inv, adjointMap_weyl_one]
  have hint : g.val.val * raising P b j = raising P b j * g.val.val := by
    apply integral_intertwining_of_rational P b g j
    rw [hgQ]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hQ
  have h := adjointMap_mul_X_of_integral_operator P b g j j 1
    (by simpa only [one_smul] using hint) R t
  rw [hgR] at h
  simp only [Int.cast_one, one_mul] at h
  exact group_fixed_conjugate_of_intertwining
    (adjointWeyl P b R i 1)
    (adjointWeyl P b R j 1 * adjointWeyl P b R i 1)
    (adjointX P b R j t) h

end Atlas.Chevalley
