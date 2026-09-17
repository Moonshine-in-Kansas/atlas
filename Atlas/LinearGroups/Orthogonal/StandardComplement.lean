import Atlas.LinearGroups.Orthogonal.Transitivity
import Atlas.LinearAlgebra.QuadraticComplementTransport

/-! # The standard hyperbolic complement is the smaller standard quadratic space -/
noncomputable section
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F]

def insertD (x : VectorD n F) : VectorD (n+1) F :=
  Sum.elim (Fin.cons 0 (fun i => x (.inl i))) (Fin.cons 0 (fun i => x (.inr i)))

def tailD (x : VectorD (n+1) F) : VectorD n F :=
  Sum.elim (fun i => x (.inl i.succ)) (fun i => x (.inr i.succ))

@[simp] theorem tail_insertD (x : VectorD n F) : tailD (insertD x) = x := by
  funext i
  cases i <;> rfl

@[simp] theorem form_insertD (x : VectorD n F) :
    formD (n+1) F (insertD x) = formD n F x := by
  simp [formD_apply, Fin.sum_univ_succ, insertD]

/-- Remove the first hyperbolic coordinate pair, retaining the quadratic form. -/
def standardComplementD :
    (Atlas.Quadratic.complementForm (formD (n+1) F) (e 0) (f 0)).IsometryEquiv
      (formD n F) where
  toFun x := tailD x.val
  invFun x := ⟨insertD x, by
    simp only [Atlas.Quadratic.mem_complement, polarD_e, polarD_f]
    exact ⟨rfl, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    have hx := x.prop
    change (formD (n+1) F).polarBilin x.val (e 0) = 0 ∧
      (formD (n+1) F).polarBilin x.val (f 0) = 0 at hx
    simp only [polarD_e, polarD_f] at hx
    funext i
    cases i with
    | inl j =>
      refine Fin.cases ?_ (fun k => rfl) j
      exact hx.2.symm
    | inr j =>
      refine Fin.cases ?_ (fun k => rfl) j
      exact hx.1.symm
  right_inv := tail_insertD
  map_add' x y := by funext i; cases i <;> rfl
  map_smul' a x := by funext i; cases i <;> rfl
  map_app' x := by
    have hx := x.prop
    change (formD (n+1) F).polarBilin x.val (e 0) = 0 ∧
      (formD (n+1) F).polarBilin x.val (f 0) = 0 at hx
    simp only [polarD_e, polarD_f] at hx
    change formD n F (tailD x.val) = formD (n+1) F x.val
    simp [formD_apply, Fin.sum_univ_succ, hx.1, hx.2, tailD]


@[simp] theorem polarB_e0 (x : VectorB (n+1) F) :
    (formB (n+1) F).polarBilin x (e 0, 0) = x.1 (.inr 0) := by
  simp only [polarB_apply, polarD_e, mul_zero, add_zero]

@[simp] theorem polarB_f0 (x : VectorB (n+1) F) :
    (formB (n+1) F).polarBilin x (f 0, 0) = x.1 (.inl 0) := by
  simp only [polarB_apply, polarD_f, mul_zero, add_zero]

/-- The last anisotropic coordinate survives removal of the first hyperbolic pair. -/
def standardComplementB :
    (Atlas.Quadratic.complementForm (formB (n+1) F) (e 0, 0) (f 0, 0)).IsometryEquiv
      (formB n F) where
  toFun x := (tailD x.val.1, x.val.2)
  invFun x := ⟨(insertD x.1, x.2), by
    simp only [Atlas.Quadratic.mem_complement, polarB_e0, polarB_f0]
    exact ⟨rfl, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    swap
    · rfl
    have hx := x.prop
    change (formB (n+1) F).polarBilin x.val (e 0, 0) = 0 ∧
      (formB (n+1) F).polarBilin x.val (f 0, 0) = 0 at hx
    simp only [polarB_e0, polarB_f0] at hx
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
    change (formB (n+1) F).polarBilin x.val (e 0, 0) = 0 ∧
      (formB (n+1) F).polarBilin x.val (f 0, 0) = 0 at hx
    simp only [polarB_e0, polarB_f0] at hx
    change formB n F (tailD x.val.1, x.val.2) = formB (n+1) F x.val
    simp [formB_apply, formD_apply, Fin.sum_univ_succ, hx.1, hx.2, tailD]


@[simp] theorem formD_e (i : Fin n) : formD n F (e i) = 0 := by
  simp [formD_apply, e, Pi.single_apply]

@[simp] theorem formD_f (i : Fin n) : formD n F (f i) = 0 := by
  simp [formD_apply, f, Pi.single_apply]

@[simp] theorem polarD_ef (i : Fin n) : (formD n F).polarBilin (e i) (f i) = 1 := by
  simp only [polarD_f, e, Pi.single_eq_same]

/-- Every actual hyperbolic complement in split D is the lower standard D space. -/
theorem complement_isometryD (u v : VectorD (n+1) F)
    (hu : formD (n+1) F u = 0) (hv : formD (n+1) F v = 0)
    (huv : (formD (n+1) F).polarBilin u v = 1) :
    Nonempty ((Atlas.Quadratic.complementForm (formD (n+1) F) u v).IsometryEquiv
      (formD n F)) := by
  obtain ⟨g⟩ := Atlas.Quadratic.nonempty_complement_isometry (formD (n+1) F)
    radicalD_eq_bot u v (e 0) (f 0) hu hv (formD_e 0) (formD_f 0) huv (polarD_ef 0)
  exact ⟨g.trans standardComplementD⟩

/-- Every actual hyperbolic complement in B is the lower standard B space, also in characteristic two. -/
theorem complement_isometryB (u v : VectorB (n+1) F)
    (hu : formB (n+1) F u = 0) (hv : formB (n+1) F v = 0)
    (huv : (formB (n+1) F).polarBilin u v = 1) :
    Nonempty ((Atlas.Quadratic.complementForm (formB (n+1) F) u v).IsometryEquiv
      (formB n F)) := by
  have he : formB (n+1) F (e 0, 0) = 0 := by simp only [formB_apply, formD_e, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  have hf : formB (n+1) F (f 0, 0) = 0 := by simp only [formB_apply, formD_f, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  have hef : (formB (n+1) F).polarBilin (e 0, 0) (f 0, 0) = 1 := by
    simp only [polarB_apply, polarD_ef, mul_zero, add_zero]
  obtain ⟨g⟩ := Atlas.Quadratic.nonempty_complement_isometry (formB (n+1) F)
    radicalB_eq_bot u v (e 0, 0) (f 0, 0) hu hv he hf huv hef
  exact ⟨g.trans standardComplementB⟩

end Atlas.Orthogonal
