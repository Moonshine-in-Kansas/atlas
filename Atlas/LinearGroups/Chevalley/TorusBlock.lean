import Atlas.LinearGroups.Chevalley.RankOne

/-! The actual torus word on its Cartan and opposite-simple-root block. -/
noncomputable section
open scoped Matrix
namespace Atlas.Chevalley
open Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

theorem adjoint_inv_mulVec_eq_of_mulVec_eq (g : Adjoint P b R)
    (a c : b.support ⊕ ι → R) (h : g.val.val *ᵥ a = c) :
    (g⁻¹).val.val *ᵥ c = a := by
  rw [← h, Matrix.mulVec_mulVec]
  have hh : (g⁻¹).val.val * g.val.val = 1 := g.val.inv_val
  rw [hh, Matrix.one_mulVec]

theorem adjointWeyl_one_inv_positive (i : b.support) :
    let := P.indexNeg
    ((adjointWeyl P b R i 1)⁻¹).val.val *ᵥ rootVector P b R i.val =
      rootVector P b R (-i.val) := by
  let := P.indexNeg
  apply adjoint_inv_mulVec_eq_of_mulVec_eq
  simpa using adjointWeyl_negative P b R i 1

theorem adjointWeyl_one_inv_negative (i : b.support) :
    let := P.indexNeg
    ((adjointWeyl P b R i 1)⁻¹).val.val *ᵥ rootVector P b R (-i.val) =
      rootVector P b R i.val := by
  let := P.indexNeg
  apply adjoint_inv_mulVec_eq_of_mulVec_eq
  simpa using adjointWeyl_positive P b R i 1

theorem adjointTorus_positive (i : b.support) (t : Rˣ) :
    (adjointTorus P b R i t).val.val *ᵥ rootVector P b R i.val =
      t.val^2 • rootVector P b R i.val := by
  let := P.indexNeg
  change ((adjointWeyl P b R i t).val.val *
      ((adjointWeyl P b R i 1)⁻¹).val.val) *ᵥ _ = _
  rw [← Matrix.mulVec_mulVec, adjointWeyl_one_inv_positive, adjointWeyl_negative]

theorem adjointTorus_negative (i : b.support) (t : Rˣ) :
    let := P.indexNeg
    (adjointTorus P b R i t).val.val *ᵥ rootVector P b R (-i.val) =
      t.inv^2 • rootVector P b R (-i.val) := by
  let := P.indexNeg
  change ((adjointWeyl P b R i t).val.val *
      ((adjointWeyl P b R i 1)⁻¹).val.val) *ᵥ _ = _
  rw [← Matrix.mulVec_mulVec, adjointWeyl_one_inv_negative, adjointWeyl_positive]

theorem adjointWeyl_one_inv_cartan (i j : b.support) :
    ((adjointWeyl P b R i 1)⁻¹).val.val *ᵥ cartanVector P b R j =
      cartanVector P b R j - ((|b.cartanMatrix i j| : ℤ) : R) •
        cartanVector P b R i := by
  apply adjoint_inv_mulVec_eq_of_mulVec_eq
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, adjointWeyl_cartan,
    adjointWeyl_cartan, b.cartanMatrix_apply_same]
  norm_num
  module

theorem adjointTorus_cartan (i j : b.support) (t : Rˣ) :
    (adjointTorus P b R i t).val.val *ᵥ cartanVector P b R j =
      cartanVector P b R j := by
  change ((adjointWeyl P b R i t).val.val *
      ((adjointWeyl P b R i 1)⁻¹).val.val) *ᵥ _ = _
  rw [← Matrix.mulVec_mulVec, adjointWeyl_one_inv_cartan, Matrix.mulVec_sub,
    Matrix.mulVec_smul, adjointWeyl_cartan, adjointWeyl_cartan,
    b.cartanMatrix_apply_same]
  norm_num
  module

end Atlas.Chevalley
