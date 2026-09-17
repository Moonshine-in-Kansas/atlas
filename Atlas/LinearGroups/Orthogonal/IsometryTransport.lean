import Atlas.LinearGroups.Orthogonal.Basic

/-! # Full quadratic isometry groups under an actual quadratic isometry -/
noncomputable section
namespace Atlas.Orthogonal
variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
variable {Q : QuadraticForm F V} {R : QuadraticForm F W}

/-- Conjugation transports the full isometry group, preserving its multiplication. -/
def isometryGroupTransport (g : Q.IsometryEquiv R) : isometrySubgroup Q ≃* isometrySubgroup R where
  toFun k := (isometryCarrierEquiv R).symm
    ((g.symm.trans (isometryCarrierEquiv Q k)).trans g)
  invFun k := (isometryCarrierEquiv Q).symm
    ((g.trans (isometryCarrierEquiv R k)).trans g.symm)
  left_inv k := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change g.symm (g (k.val (g.symm (g x)))) = k.val x
    rw [g.symm_apply_apply, g.symm_apply_apply]
  right_inv k := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change g (g.symm (k.val (g (g.symm x)))) = k.val x
    rw [g.apply_symm_apply, g.apply_symm_apply]
  map_mul' k l := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change g (k.val (l.val (g.symm x))) = g (k.val (g.symm (g (l.val (g.symm x)))))
    rw [g.symm_apply_apply]

end Atlas.Orthogonal
