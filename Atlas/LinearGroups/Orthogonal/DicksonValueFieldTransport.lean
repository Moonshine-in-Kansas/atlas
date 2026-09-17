import Atlas.LinearGroups.Orthogonal.DicksonFieldTransport
import Mathlib.LinearAlgebra.Dimension.Basic

/-! # Actual residual-rank preservation under field transport -/
noncomputable section
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F K V W : Type*} [Field F] [Field K]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module K W]
variable (e : F ≃+* K) (T : V ≃ₛₗ[RingHomClass.toRingHom e] W)
variable (Q : QuadraticForm F V) (R : QuadraticForm K W)
variable (hQ : ∀ x, R (T x) = e (Q x)) (g : isometrySubgroup Q)

/-- Transport restricts to the actual residual subspaces, not merely to their dimensions. -/
def semilinearResidualEquiv :
    residual Q (isometryCarrierEquiv Q g) ≃ₛₗ[RingHomClass.toRingHom e]
      residual R (isometryCarrierEquiv R (semilinearIsometryGroupTransport e T Q R hQ g)) where
  toFun x := ⟨T x.val, by
    obtain ⟨y, hy⟩ := x.prop
    refine ⟨T y, ?_⟩
    change T y - T (g.val (T.symm (T y))) = T x.val
    change y - g.val y = x.val at hy
    rw [T.symm_apply_apply, ← map_sub, hy]⟩
  invFun x := ⟨T.symm x.val, by
    obtain ⟨y, hy⟩ := x.prop
    refine ⟨T.symm y, ?_⟩
    change T.symm y - g.val (T.symm y) = T.symm x.val
    change y - T (g.val (T.symm y)) = x.val at hy
    rw [← hy, map_sub, T.symm_apply_apply]⟩
  left_inv x := by apply Subtype.ext; exact T.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact T.apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact map_add T x.val y.val
  map_smul' c x := by apply Subtype.ext; exact map_smulₛₗ T c x.val

/-- The actual integer residual dimension is preserved through arbitrary field equivalence. -/
theorem residual_finrank_semilinear_transport :
    Module.finrank K
      (residual R (isometryCarrierEquiv R (semilinearIsometryGroupTransport e T Q R hQ g))) =
      Module.finrank F (residual Q (isometryCarrierEquiv Q g)) := by
  let S := semilinearResidualEquiv e T Q R hQ g
  have h := _root_.lift_rank_eq_of_equiv_equiv e S.toAddEquiv e.bijective
    (fun c x => S.map_smulₛₗ c x)
  simpa only [Cardinal.toNat_lift, Module.finrank] using (congrArg Cardinal.toNat h).symm

/-- The intrinsic residual parity is preserved, without identifying its kernel first. -/
theorem dicksonValue_semilinear_transport :
    dicksonValue R (semilinearIsometryGroupTransport e T Q R hQ g) = dicksonValue Q g := by
  exact congrArg (fun n : ℕ => (n : ZMod 2))
    (residual_finrank_semilinear_transport e T Q R hQ g)

variable {n : ℕ}

theorem residual_finrank_fieldEquivFullD (e : F ≃+* K) (g : O_DPlus n F) :
    Module.finrank K (residual (formD n K)
      (isometryCarrierEquiv _ (fieldEquivFullD e g))) =
      Module.finrank F (residual (formD n F) (isometryCarrierEquiv _ g)) :=
  residual_finrank_semilinear_transport e (fieldCoordinatesD e) _ _ (fieldCoordinatesD_form e) g

theorem dicksonValue_fieldEquivFullD (e : F ≃+* K) (g : O_DPlus n F) :
    dicksonValue (formD n K) (fieldEquivFullD e g) = dicksonValue (formD n F) g :=
  dicksonValue_semilinear_transport e (fieldCoordinatesD e) _ _ (fieldCoordinatesD_form e) g

/-- The full Dickson characters commute with the prescribed field transport in every characteristic. -/
theorem fullDicksonD_field_transport (n : ℕ) (e : F ≃+* K) (g : O_DPlus (n + 3) F) :
    fullDicksonD n (fieldEquivFullD e g) = fullDicksonD n g := by
  apply Multiplicative.toAdd.injective
  exact dicksonValue_fieldEquivFullD e g
end Atlas.Orthogonal
