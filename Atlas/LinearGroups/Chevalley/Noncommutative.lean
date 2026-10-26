import Atlas.LinearGroups.Chevalley.RankOne

/-! Two opposite root elements do not commute, in every characteristic. -/

noncomputable section
open scoped Matrix
open RootPairing.GeckConstruction
namespace Atlas.Chevalley
open Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R] [Nontrivial R]

/-- The Cartan coordinate distinguishes the two opposite-root products.
This uses no division and also works in characteristics two and three. -/
theorem adjointX_one_mul_adjointY_one_ne (i : b.support) :
    adjointX P b R i 1 * adjointY P b R i 1 ≠
      adjointY P b R i 1 * adjointX P b R i 1 := by
  let := P.indexNeg
  intro h
  have he := congrArg (fun g : Adjoint P b R =>
    (g.val.val *ᵥ rootVector P b R i.val) (Sum.inl i)) h
  change ((raisingExponential P b R i 1 * (loweringRootElement P b R i 1).val) *ᵥ
      rootVector P b R i.val) (Sum.inl i) =
    (((loweringRootElement P b R i 1).val * raisingExponential P b R i 1) *ᵥ
      rootVector P b R i.val) (Sum.inl i) at he
  rw [loweringRootElement_val, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    loweringExponential_positive, raisingExponential_positive] at he
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, raisingExponential_positive,
    raisingExponential_cartan, raisingExponential_negative,
    loweringExponential_positive] at he
  have h21 : (1 : R) + 1 = 1 := by
    simpa [rootVector, cartanVector, u, v, Pi.single_apply] using he
  have h10 : (1 : R) = 0 := by
    apply add_left_cancel (a := (1 : R))
    simpa using h21
  exact one_ne_zero h10

/-- Every nonempty-root adjoint model is noncommutative over a nontrivial ring. -/
theorem adjoint_not_commutative [Nonempty b.support] :
    ¬ IsMulCommutative (Adjoint P b R) := by
  intro h
  let i : b.support := Classical.choice inferInstance
  exact adjointX_one_mul_adjointY_one_ne P b R i
    (h.is_comm.comm (adjointX P b R i 1) (adjointY P b R i 1))

end Atlas.Chevalley
