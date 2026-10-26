import Atlas.LinearGroups.Chevalley.AdjointWeylWordRoots
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-! Length-four and length-six braids in the actual adjoint subgroup.
The root columns use the integral inversion-root calculation. The Cartan
columns are proved here on the actual Geck basis, without a complement,
Cartan-matrix inverse, projection-injectivity or Coxeter assumption. -/

noncomputable section
open scoped Matrix
namespace Atlas.Chevalley
open Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- The short node is i: Cartan(i,j)=-1 and Cartan(j,i)=-2. -/
theorem adjointWeyl_b2_braid_cartan (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2)
    (k : b.support) :
    ((adjointWeyl P b R i 1).val.val * (adjointWeyl P b R j 1).val.val *
      (adjointWeyl P b R i 1).val.val * (adjointWeyl P b R j 1).val.val) *ᵥ
        cartanVector P b R k =
      ((adjointWeyl P b R j 1).val.val * (adjointWeyl P b R i 1).val.val *
        (adjointWeyl P b R j 1).val.val * (adjointWeyl P b R i 1).val.val) *ᵥ
          cartanVector P b R k := by
  simp only [← Matrix.mulVec_mulVec, adjointWeyl_cartan,
    Matrix.mulVec_sub, Matrix.mulVec_smul, b.cartanMatrix_apply_same, hij, hji]
  norm_num <;> module

/-- Actual length-four equality, including every Cartan and root coordinate. -/
theorem adjointWeyl_b2_braid (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    adjointWeyl P b R i 1 * adjointWeyl P b R j 1 *
      adjointWeyl P b R i 1 * adjointWeyl P b R j 1 =
        adjointWeyl P b R j 1 * adjointWeyl P b R i 1 *
          adjointWeyl P b R j 1 * adjointWeyl P b R i 1 := by
  have hv (k : ι) : rootVector P b R k = Pi.single (Sum.inr k) 1 := by
    ext row
    by_cases h : row = Sum.inr k <;>
      simp [rootVector, RootPairing.GeckConstruction.v, Function.comp_def, Pi.single_apply, h]
  have hu (k : b.support) : cartanVector P b R k = Pi.single (Sum.inl k) 1 := by
    ext row
    by_cases h : row = Sum.inl k <;>
      simp [cartanVector, RootPairing.GeckConstruction.u, Function.comp_def, Pi.single_apply, h]
  apply Subtype.ext
  apply Units.ext
  change (adjointWeyl P b R i 1).val.val * (adjointWeyl P b R j 1).val.val *
      (adjointWeyl P b R i 1).val.val * (adjointWeyl P b R j 1).val.val =
    (adjointWeyl P b R j 1).val.val * (adjointWeyl P b R i 1).val.val *
      (adjointWeyl P b R j 1).val.val * (adjointWeyl P b R i 1).val.val
  apply Matrix.ext_of_mulVec_single
  intro k
  cases k with
  | inl k =>
    rw [← hu k]
    exact adjointWeyl_b2_braid_cartan P b R i j hij hji k
  | inr k =>
    rw [← hv k]
    simpa only [adjointWeylWord, mul_one, ← mul_assoc, Subgroup.coe_mul,
      Units.val_mul] using adjointWeylWord_four_root P b R i j hij hji k

/-- The short node is i: Cartan(i,j)=-1 and Cartan(j,i)=-3. -/
theorem adjointWeyl_g2_braid_cartan (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3)
    (k : b.support) :
    ((adjointWeyl P b R i 1).val.val * (adjointWeyl P b R j 1).val.val *
      (adjointWeyl P b R i 1).val.val * (adjointWeyl P b R j 1).val.val *
      (adjointWeyl P b R i 1).val.val * (adjointWeyl P b R j 1).val.val) *ᵥ
        cartanVector P b R k =
      ((adjointWeyl P b R j 1).val.val * (adjointWeyl P b R i 1).val.val *
        (adjointWeyl P b R j 1).val.val * (adjointWeyl P b R i 1).val.val *
        (adjointWeyl P b R j 1).val.val * (adjointWeyl P b R i 1).val.val) *ᵥ
          cartanVector P b R k := by
  simp only [← Matrix.mulVec_mulVec, adjointWeyl_cartan,
    Matrix.mulVec_sub, Matrix.mulVec_smul, b.cartanMatrix_apply_same, hij, hji]
  norm_num <;> module

/-- Actual length-six equality over every commutative coefficient ring. -/
theorem adjointWeyl_g2_braid (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    adjointWeyl P b R i 1 * adjointWeyl P b R j 1 *
      adjointWeyl P b R i 1 * adjointWeyl P b R j 1 *
      adjointWeyl P b R i 1 * adjointWeyl P b R j 1 =
        adjointWeyl P b R j 1 * adjointWeyl P b R i 1 *
          adjointWeyl P b R j 1 * adjointWeyl P b R i 1 *
          adjointWeyl P b R j 1 * adjointWeyl P b R i 1 := by
  have hv (k : ι) : rootVector P b R k = Pi.single (Sum.inr k) 1 := by
    ext row
    by_cases h : row = Sum.inr k <;>
      simp [rootVector, RootPairing.GeckConstruction.v, Function.comp_def, Pi.single_apply, h]
  have hu (k : b.support) : cartanVector P b R k = Pi.single (Sum.inl k) 1 := by
    ext row
    by_cases h : row = Sum.inl k <;>
      simp [cartanVector, RootPairing.GeckConstruction.u, Function.comp_def, Pi.single_apply, h]
  apply Subtype.ext
  apply Units.ext
  change (adjointWeyl P b R i 1).val.val * (adjointWeyl P b R j 1).val.val *
      (adjointWeyl P b R i 1).val.val * (adjointWeyl P b R j 1).val.val *
      (adjointWeyl P b R i 1).val.val * (adjointWeyl P b R j 1).val.val =
    (adjointWeyl P b R j 1).val.val * (adjointWeyl P b R i 1).val.val *
      (adjointWeyl P b R j 1).val.val * (adjointWeyl P b R i 1).val.val *
      (adjointWeyl P b R j 1).val.val * (adjointWeyl P b R i 1).val.val
  apply Matrix.ext_of_mulVec_single
  intro k
  cases k with
  | inl k =>
    rw [← hu k]
    exact adjointWeyl_g2_braid_cartan P b R i j hij hji k
  | inr k =>
    rw [← hv k]
    simpa only [adjointWeylWord, mul_one, ← mul_assoc, Subgroup.coe_mul,
      Units.val_mul] using adjointWeylWord_six_root P b R i j hij hji k

end Atlas.Chevalley
