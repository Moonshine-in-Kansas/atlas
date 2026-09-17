import Atlas.LinearGroups.Orthogonal.Basic

/-! # Semilinear transport of full quadratic isometry groups -/
noncomputable section
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
namespace Atlas.Orthogonal
variable {F K V W : Type*} [Field F] [Field K]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module K W]
variable (e : F ≃+* K) (T : V ≃ₛₗ[RingHomClass.toRingHom e] W)
variable (Q : QuadraticForm F V) (R : QuadraticForm K W)
variable (hQ : ∀ x, R (T x) = e (Q x))

/-- Conjugation along a specified semilinear quadratic isometry. -/
def semilinearIsometryGroupTransport : isometrySubgroup Q ≃* isometrySubgroup R where
  toFun g := ⟨(T.symm.trans g.val).trans T, by
    intro x
    change R (T (g.val (T.symm x))) = R x
    rw [hQ, g.prop, ← hQ, T.apply_symm_apply]⟩
  invFun g := ⟨(T.trans g.val).trans T.symm, by
    intro x
    apply e.injective
    rw [← hQ]
    change R (T (T.symm (g.val (T x)))) = e (Q x)
    rw [T.apply_symm_apply, g.prop, hQ]⟩
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change T.symm (T (g.val (T.symm (T x)))) = g.val x
    rw [T.symm_apply_apply, T.symm_apply_apply]
  right_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change T (T.symm (g.val (T (T.symm x)))) = g.val x
    rw [T.apply_symm_apply, T.apply_symm_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change T (g.val (h.val (T.symm x))) = T (g.val (T.symm (T (h.val (T.symm x)))))
    rw [T.symm_apply_apply]

end Atlas.Orthogonal
