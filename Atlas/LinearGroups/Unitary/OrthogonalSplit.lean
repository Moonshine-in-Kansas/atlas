import Atlas.LinearGroups.Unitary.Hermitian
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Orthogonal splitting at an actual norm-one vector, in all characteristics. -/
noncomputable section
namespace Atlas.Unitary
open Atlas.FiniteQuadratic
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

/-- The actual orthogonal complement of a vector for the retained Hermitian form. -/
def perp (v : Fin n → K) : Submodule K (Fin n → K) where
  carrier := {w | hermitian F K w v = 0}
  zero_mem' := hermitian_zero_left v
  add_mem' := by
    intro x y hx hy
    change hermitian F K (x + y) v = 0
    rw [hermitian_add_left, hx, hy, add_zero]
  smul_mem' := by
    intro a x hx
    change hermitian F K (a • x) v = 0
    rw [hermitian_smul_left, hx, mul_zero]

@[simp] theorem mem_perp (v w : Fin n → K) :
    w ∈ perp F K v ↔ hermitian F K w v = 0 := Iff.rfl

/-- Projection onto the actual complement, rather than a dimension-only replacement. -/
def perpProjection (v : Fin n → K) (hv : hermitian F K v v = 1) :
    (Fin n → K) →ₗ[K] perp F K v where
  toFun w := ⟨w - hermitian F K w v • v, by
    change hermitian F K (w - hermitian F K w v • v) v = 0
    rw [sub_eq_add_neg]
    rw [hermitian_add_left]
    have hn : -(hermitian F K w v • v) = (-hermitian F K w v) • v := by simp
    rw [hn, hermitian_smul_left, hv, mul_one, add_neg_cancel]⟩
  map_add' x y := by
    apply Subtype.ext
    change x + y - hermitian F K (x + y) v • v =
      (x - hermitian F K x v • v) + (y - hermitian F K y v • v)
    simp only [hermitian_add_left, add_smul]
    module
  map_smul' a x := by
    apply Subtype.ext
    change a • x - hermitian F K (a • x) v • v = a • (x - hermitian F K x v • v)
    simp only [hermitian_smul_left, smul_sub, mul_smul]

/-- Splitting off the given norm-one line, with explicit inverse. -/
def orthogonalSplit (v : Fin n → K) (hv : hermitian F K v v = 1) :
    (K × perp F K v) ≃ₗ[K] (Fin n → K) where
  toFun p := p.1 • v + p.2.val
  invFun w := (hermitian F K w v, perpProjection F K v hv w)
  left_inv p := by
    apply Prod.ext
    · simp [hermitian_add_left, hermitian_smul_left, hv, ((mem_perp F K v p.2.val).mp p.2.property)]
    · apply Subtype.ext
      simp only [perpProjection, LinearMap.coe_mk, AddHom.coe_mk,
        hermitian_add_left, hermitian_smul_left, hv, mul_one,
        ((mem_perp F K v p.2.val).mp p.2.property), add_zero]
      module
  right_inv w := by
    change hermitian F K w v • v + (w - hermitian F K w v • v) = w
    module
  map_add' p q := by dsimp; rw [add_smul]; module
  map_smul' a p := by dsimp; rw [smul_add, smul_smul]

/-- The decomposition is orthogonal for the original Hermitian form. -/
theorem orthogonalSplit_hermitian (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 1)
    (p q : K × perp F K v) :
    hermitian F K (orthogonalSplit F K v hv p) (orthogonalSplit F K v hv q) =
      p.1 * conjugation F K q.1 + hermitian F K p.2.val q.2.val := by
  have hcross : hermitian F K v q.2.val = 0 := by
    rw [← hermitian_symmetry hdeg, ((mem_perp F K v q.2.val).mp q.2.property), map_zero]
  change hermitian F K (p.1 • v + p.2.val) (q.1 • v + q.2.val) = _
  simp only [hermitian_add_left, hermitian_add_right, hermitian_smul_left,
    hermitian_smul_right, hv, hcross, ((mem_perp F K v p.2.val).mp p.2.property), mul_zero, mul_one,
    add_zero, zero_add]
  ring

/-- Nondegeneracy is inherited by the actual orthogonal complement. -/
theorem perp_nondegenerate (v : Fin n → K) (hv : hermitian F K v v = 1)
    (x : perp F K v) (hx : ∀ y : perp F K v, hermitian F K x.val y.val = 0) : x = 0 := by
  apply Subtype.ext
  apply hermitian_nondegenerate (F := F)
  intro w
  have hw := (orthogonalSplit F K v hv).apply_symm_apply w
  rw [← hw]
  change hermitian F K x.val (_ • v + _) = 0
  rw [hermitian_add_right, hermitian_smul_right, ((mem_perp F K v x.val).mp x.property),
    mul_zero, zero_add]
  exact hx _

/-- The complement has codimension one. -/
theorem finrank_perp (v : Fin n → K) (hv : hermitian F K v v = 1) :
    1 + Module.finrank K (perp F K v) = n := by
  have h := (orthogonalSplit F K v hv).finrank_eq
  simpa using h
end Atlas.Unitary
