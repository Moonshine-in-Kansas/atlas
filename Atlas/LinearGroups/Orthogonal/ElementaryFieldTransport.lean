import Atlas.LinearGroups.Orthogonal.FieldTransport
import Atlas.LinearGroups.Orthogonal.Elementary
import Mathlib.Algebra.Group.Subgroup.Map

/-! # Actual semilinear transport of elementary quadratic groups -/
noncomputable section
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F K V W : Type*} [Field F] [Field K]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module K W]
variable (e : F ≃+* K) (T : V ≃ₛₗ[RingHomClass.toRingHom e] W)
variable (Q : QuadraticForm F V) (R : QuadraticForm K W)
variable (hQ : ∀ x, R (T x) = e (Q x))

include hQ in
theorem semilinear_polar_transport (x y : V) :
    R.polarBilin (T x) (T y) = e (Q.polarBilin x y) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add,
    hQ, map_sub]

include hQ in
theorem semilinear_siegel_covariant (u v x : V) :
    T (siegel Q u v x) = siegel R (T u) (T v) (T x) := by
  simp only [siegel, map_sub, map_add, map_smulₛₗ, semilinear_polar_transport e T Q R hQ,
    hQ, map_mul, RingHom.coe_coe]

/-- The full transport sends each actual elementary generator to its transported generator. -/
theorem semilinear_siegelElement (u v : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    semilinearIsometryGroupTransport e T Q R hQ (siegelElement Q u v hu huv) =
      siegelElement R (T u) (T v) (by rw [hQ, hu, map_zero])
        (by rw [semilinear_polar_transport e T Q R hQ, huv, map_zero]) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change T (siegel Q u v (T.symm x)) = siegel R (T u) (T v) x
  rw [semilinear_siegel_covariant e T Q R hQ, T.apply_symm_apply]

/-- Equality of actual generated subgroups under transport; no generation target is assumed. -/
theorem semilinear_elementary_map :
    (elementarySubgroup Q).map (semilinearIsometryGroupTransport e T Q R hQ).toMonoidHom =
      elementarySubgroup R := by
  rw [elementarySubgroup, MonoidHom.map_closure, elementarySubgroup]
  congr 1
  ext g
  constructor
  · rintro ⟨s, ⟨u, v, hu, huv, rfl⟩, rfl⟩
    refine ⟨T u, T v, ?_, ?_, semilinear_siegelElement e T Q R hQ u v hu huv⟩
    · rw [hQ, hu, map_zero]
    · rw [semilinear_polar_transport e T Q R hQ, huv, map_zero]
  · rintro ⟨u, v, hu, huv, rfl⟩
    have hpre : Q (T.symm u) = 0 := by
      apply e.injective
      rw [← hQ, T.apply_symm_apply, hu, map_zero]
    have hpol : Q.polarBilin (T.symm u) (T.symm v) = 0 := by
      apply e.injective
      rw [← semilinear_polar_transport e T Q R hQ, T.apply_symm_apply,
        T.apply_symm_apply, huv, map_zero]
    refine ⟨siegelElement Q (T.symm u) (T.symm v) hpre hpol,
      ⟨T.symm u, T.symm v, hpre, hpol, rfl⟩, ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change T (siegel Q (T.symm u) (T.symm v) (T.symm x)) = siegel R u v x
    rw [semilinear_siegel_covariant e T Q R hQ, T.apply_symm_apply,
      T.apply_symm_apply, T.apply_symm_apply]


def semilinearElementaryEquiv : elementarySubgroup Q ≃* elementarySubgroup R :=
  (semilinearIsometryGroupTransport e T Q R hQ).subgroupMap (elementarySubgroup Q) |>.trans
    (MulEquiv.subgroupCongr (semilinear_elementary_map e T Q R hQ))

def fieldEquivElementaryB {n : ℕ} (e : F ≃+* K) :
    elementarySubgroup (formB n F) ≃* elementarySubgroup (formB n K) :=
  semilinearElementaryEquiv e (fieldCoordinatesB e) _ _ (fieldCoordinatesB_form e)

def fieldEquivElementaryD {n : ℕ} (e : F ≃+* K) :
    elementarySubgroup (formD n F) ≃* elementarySubgroup (formD n K) :=
  semilinearElementaryEquiv e (fieldCoordinatesD e) _ _ (fieldCoordinatesD_form e)
end Atlas.Orthogonal
