import Atlas.LinearAlgebra.QuadraticWittTwo
import Atlas.LinearAlgebra.QuadraticComplementTransport

/-! # Transporting perpendicular hyperbolic witnesses through actual complement isometries -/
noncomputable section
namespace Atlas.Quadratic
variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
variable (Q : QuadraticForm F V) (R : QuadraticForm F W)

/-- An actual quadratic isometry transports the unhalved polar form. -/
theorem isometry_between_polar (g : Q.IsometryEquiv R) (x y : V) :
    R.polarBilin (g x) (g y) = Q.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, g.map_app]

theorem complementForm_polar (e f : V) (x y : complement Q e f) :
    (complementForm Q e f).polarBilin x y = Q.polarBilin x.val y.val := by
  rw [complementForm, QuadraticMap.polarBilin_comp]
  rfl

/-- A two-pair standard complement supplies a hyperbolic pair perpendicular to any parameter. -/
theorem complement_perpendicular_pair (e f : V)
    (g : (complementForm Q e f).IsometryEquiv R) (H : WittTwoFrame R)
    (hR : R.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0) (v : complement Q e f) :
    ∃ a b : complement Q e f, Q a.val = 0 ∧ Q b.val = 0 ∧ Q.polarBilin a.val b.val = 1 ∧
      Q.polarBilin v.val a.val = 0 ∧ Q.polarBilin v.val b.val = 0 := by
  obtain ⟨a, b, ha, hb, hab, hav, hbv⟩ := hyperbolic_pair_in_perpendicular R H hR h2 (g v)
  refine ⟨g.symm a, g.symm b, (g.symm.map_app a).trans ha, (g.symm.map_app b).trans hb, ?_, ?_, ?_⟩
  · rw [← complementForm_polar Q e f]
    exact (isometry_between_polar R (complementForm Q e f) g.symm a b).trans hab
  · rw [← complementForm_polar Q e f]
    have h := isometry_between_polar (complementForm Q e f) R g v (g.symm a)
    rw [g.apply_symm_apply, polar_swap R (g v) a] at h
    exact h.symm.trans hav
  · rw [← complementForm_polar Q e f]
    have h := isometry_between_polar (complementForm Q e f) R g v (g.symm b)
    rw [g.apply_symm_apply, polar_swap R (g v) b] at h
    exact h.symm.trans hbv

end Atlas.Quadratic
