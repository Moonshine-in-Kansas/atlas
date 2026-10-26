import Atlas.LinearGroups.Unitary.OrthogonalSplit
import Atlas.LinearGroups.Unitary.NormOneTransport

/-! The orthogonal complement of a norm-one vector is actually isometric to the
standard Hermitian space of one lower dimension. The proof uses explicit unitary
transport, rather than a dimension-only identification. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

/-- The first coordinate unit vector. -/
def firstVector (n : ℕ) : Fin (n + 1) → K := Pi.single 0 1

@[simp] theorem hermitian_firstVector (w : Fin (n + 1) → K) :
    hermitian F K w (firstVector K n) = w 0 := hermitian_single_right w 0

@[simp] theorem firstVector_norm :
    hermitian F K (firstVector K n) (firstVector K n) = 1 := by
  simp [firstVector]

/-- In standard coordinates, the first-coordinate complement is given by
inserting an initial zero, with inverse deleting that coordinate. -/
def firstPerpEquiv : (Fin n → K) ≃ₗ[K] perp F K (firstVector K n) where
  toFun x := ⟨Fin.cons 0 x, by simp⟩
  invFun x := Fin.tail x.val
  left_inv x := Fin.tail_cons _ _
  right_inv x := by
    apply Subtype.ext
    have hx : x.val 0 = 0 := by
      simpa only [mem_perp, hermitian_firstVector] using x.property
    change Fin.cons 0 (Fin.tail x.val) = x.val
    rw [← hx, Fin.cons_self_tail]
  map_add' x y := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' a x := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem firstPerpEquiv_preserves (x y : Fin n → K) :
    hermitian F K (firstPerpEquiv F K x).val (firstPerpEquiv F K y).val =
      hermitian F K x y := by
  simp [hermitian, firstPerpEquiv, Fin.sum_univ_succ]

/-- Restriction of an actual Hermitian isometry to actual orthogonal complements. -/
def perpEquiv {v w : Fin n → K} (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (he : ∀ x y, hermitian F K (e x) (e y) = hermitian F K x y) (hev : e v = w) :
    perp F K v ≃ₗ[K] perp F K w where
  toFun x := ⟨e x.val, by
    change hermitian F K (e x.val) w = 0
    rw [← hev, he]
    exact x.property⟩
  invFun y := ⟨e.symm y.val, by
    change hermitian F K (e.symm y.val) v = 0
    rw [← he, e.apply_symm_apply, hev]
    exact y.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val
  map_add' x y := by apply Subtype.ext; exact e.map_add x.val y.val
  map_smul' a x := by apply Subtype.ext; exact e.map_smul a x.val

theorem perpEquiv_preserves {v w : Fin n → K}
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (he : ∀ x y, hermitian F K (e x) (e y) = hermitian F K x y) (hev : e v = w)
    (x y : perp F K v) :
    hermitian F K (perpEquiv F K e he hev x).val (perpEquiv F K e he hev y).val =
      hermitian F K x.val y.val := he x.val y.val

/-- An actual linear equivalence preserving the form on the actual complement. -/
theorem exists_standardComplement (hdeg : Module.finrank F K = 2)
    (v : Fin (n + 1) → K) (hv : hermitian F K v v = 1) :
    ∃ e : (Fin n → K) ≃ₗ[K] perp F K v,
      ∀ x y, hermitian F K (e x).val (e y).val = hermitian F K x y := by
  obtain ⟨g, hg⟩ := exists_unitary_map hdeg (firstVector K n) v (firstVector_norm F K) hv
  let := conjugationStarRing F K hdeg
  let e := Matrix.UnitaryGroup.toLinearEquiv g
  have he : ∀ x y, hermitian F K (e x) (e y) = hermitian F K x y :=
    u_preserves_hermitian hdeg g
  have hev : e (firstVector K n) = v := hg
  refine ⟨(firstPerpEquiv F K).trans (perpEquiv F K e he hev), ?_⟩
  intro x y
  change hermitian F K (e (firstPerpEquiv F K x).val) (e (firstPerpEquiv F K y).val) = _
  rw [he, firstPerpEquiv_preserves]
end Atlas.Unitary
