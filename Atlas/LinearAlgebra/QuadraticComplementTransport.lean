import Atlas.LinearAlgebra.QuadraticPairTransport

/-! # Isometries of actual hyperbolic perpendicular complements -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

def complementForm (e f : V) : QuadraticForm F (complement Q e f) :=
  Q.comp (complement Q e f).subtype

/-- Restrict an ambient isometry carrying one marked pair to another. -/
def complementTransport (g : Q.IsometryEquiv Q) (e f u v : V)
    (he : g e = u) (hf : g f = v) :
    (complementForm Q e f).IsometryEquiv (complementForm Q u v) where
  toFun x := ⟨g x.val, by
    change Q.polarBilin (g x.val) u = 0 ∧ Q.polarBilin (g x.val) v = 0
    rw [← he, ← hf, isometry_polar, isometry_polar]
    exact x.prop⟩
  invFun x := ⟨g.symm x.val, by
    change Q.polarBilin (g.symm x.val) e = 0 ∧ Q.polarBilin (g.symm x.val) f = 0
    have he' : g.symm u = e := by rw [← he, g.symm_apply_apply]
    have hf' : g.symm v = f := by rw [← hf, g.symm_apply_apply]
    rw [← he', ← hf', isometry_polar, isometry_polar]
    exact x.prop⟩
  left_inv x := Subtype.ext (g.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add g x.val y.val)
  map_smul' a x := Subtype.ext (map_smul g a x.val)
  map_app' x := g.map_app x.val

/-- Hyperbolic complements are isometric by restriction of an actual ambient isometry. -/
theorem nonempty_complement_isometry (hQ : Q.radical = ⊥) (e f u v : V)
    (he : Q e = 0) (hf : Q f = 0) (hu : Q u = 0) (hv : Q v = 0)
    (hef : Q.polarBilin e f = 1) (huv : Q.polarBilin u v = 1) :
    Nonempty ((complementForm Q e f).IsometryEquiv (complementForm Q u v)) := by
  obtain ⟨g, hg, hk⟩ := exists_isometry_hyperbolic_pair Q hQ e f u v he hf hu hv hef huv
  exact ⟨complementTransport Q g e f u v hg hk⟩

end Atlas.Quadratic
