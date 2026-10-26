import Atlas.LinearGroups.Orthogonal.Minus.Geometry
import Atlas.LinearGroups.Orthogonal.StandardComplement

/-! Actual minus-form hyperbolic complements retain the same norm-plane tail. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {n : ℕ} {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

@[simp] theorem polar_e0 (hdeg : Module.finrank F K = 2) (x : Vector (n+1) F K) :
    (form hdeg (n+1)).polarBilin x (e 0, 0) = x.1 (.inr 0) := by
  simp only [polar_apply, polarD_e, map_zero, add_zero]

@[simp] theorem polar_f0 (hdeg : Module.finrank F K = 2) (x : Vector (n+1) F K) :
    (form hdeg (n+1)).polarBilin x (f 0, 0) = x.1 (.inl 0) := by
  simp only [polar_apply, polarD_f, map_zero, add_zero]

/-- The last anisotropic coordinate survives removal of the first hyperbolic pair. -/
def standardComplement (hdeg : Module.finrank F K = 2) :
    (Atlas.Quadratic.complementForm (form hdeg (n+1)) (e 0, 0) (f 0, 0)).IsometryEquiv
      (form hdeg n) where
  toFun x := (tailD x.val.1, x.val.2)
  invFun x := ⟨(insertD x.1, x.2), by
    simp only [Atlas.Quadratic.mem_complement, polar_e0, polar_f0]
    exact ⟨rfl, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    swap
    · rfl
    have hx := x.prop
    change (form hdeg (n+1)).polarBilin x.val (e 0, 0) = 0 ∧
      (form hdeg (n+1)).polarBilin x.val (f 0, 0) = 0 at hx
    simp only [polar_e0, polar_f0] at hx
    funext i
    cases i with
    | inl j =>
      refine Fin.cases ?_ (fun k => rfl) j
      exact hx.2.symm
    | inr j =>
      refine Fin.cases ?_ (fun k => rfl) j
      exact hx.1.symm
  right_inv x := Prod.ext (tail_insertD x.1) rfl
  map_add' x y := by
    apply Prod.ext
    swap
    · rfl
    funext i
    cases i <;> rfl
  map_smul' a x := by
    apply Prod.ext
    swap
    · rfl
    funext i
    cases i <;> rfl
  map_app' x := by
    have hx := x.prop
    change (form hdeg (n+1)).polarBilin x.val (e 0, 0) = 0 ∧
      (form hdeg (n+1)).polarBilin x.val (f 0, 0) = 0 at hx
    simp only [polar_e0, polar_f0] at hx
    change form hdeg n (tailD x.val.1, x.val.2) = form hdeg (n+1) x.val
    simp [form_apply, formD_apply, Fin.sum_univ_succ, hx.1, hx.2, tailD]


/-- Every marked hyperbolic-pair complement is the lower minus form, by actual
ambient pair transport followed by the explicit coordinate deletion isometry. -/
theorem complement_isometry (hdeg : Module.finrank F K = 2)
    (u v : Vector (n+1) F K)
    (hu : form hdeg (n+1) u = 0) (hv : form hdeg (n+1) v = 0)
    (huv : (form hdeg (n+1)).polarBilin u v = 1) :
    Nonempty ((Atlas.Quadratic.complementForm (form hdeg (n+1)) u v).IsometryEquiv
      (form hdeg n)) := by
  have he : form hdeg (n+1) (e 0, 0) = 0 := by simp only [form_apply, formD_e, ← normForm_apply hdeg, map_zero, add_zero]
  have hf : form hdeg (n+1) (f 0, 0) = 0 := by simp only [form_apply, formD_f, ← normForm_apply hdeg, map_zero, add_zero]
  have hef : (form hdeg (n+1)).polarBilin (e 0, 0) (f 0, 0) = 1 := by
    simp only [polar_f0, e, Pi.single_eq_same]
  obtain ⟨g⟩ := Atlas.Quadratic.nonempty_complement_isometry (form hdeg (n+1))
    (radical_eq_bot hdeg (n+1)) u v (e 0, 0) (f 0, 0) hu hv he hf huv hef
  exact ⟨g.trans (standardComplement hdeg)⟩
end Atlas.Orthogonal.Minus
