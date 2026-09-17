import Atlas.LinearAlgebra.QuadraticComplementWitness

/-! # Nondegeneracy under an actual quadratic isometry -/
namespace Atlas.Quadratic
variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
variable (Q : QuadraticForm F V) (R : QuadraticForm F W)

/-- Pull back polar nondegeneracy along an actual quadratic isometry. -/
theorem isometry_between_nondegenerate (g : Q.IsometryEquiv R)
    (hR : R.polarBilin.Nondegenerate) : Q.polarBilin.Nondegenerate := by
  constructor
  · intro x hx
    apply g.injective
    rw [map_zero]
    apply hR.1
    intro y
    have h := isometry_between_polar Q R g x (g.symm y)
    rw [g.apply_symm_apply] at h
    exact h.trans (hx _)
  · intro x hx
    apply g.injective
    rw [map_zero]
    apply hR.2
    intro y
    have h := isometry_between_polar Q R g (g.symm y) x
    rw [g.apply_symm_apply] at h
    exact h.trans (hx _)

theorem isometry_between_nondegenerate_iff (g : Q.IsometryEquiv R) :
    Q.polarBilin.Nondegenerate ↔ R.polarBilin.Nondegenerate :=
  ⟨isometry_between_nondegenerate R Q g.symm, isometry_between_nondegenerate Q R g⟩

end Atlas.Quadratic
