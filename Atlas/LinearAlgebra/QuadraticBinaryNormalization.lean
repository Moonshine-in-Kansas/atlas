import Atlas.Algebra.FiniteFieldBinaryRepresentation
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Tactic

/-! # A binary normalization step with exact determinant, in finite odd characteristic -/
noncomputable section
namespace Atlas.Quadratic
variable {F : Type*} [Field F]

/-- The binary quadratic form on an actual product space. -/
def binaryForm (a b : F) : QuadraticForm F (F × F) :=
  a • (QuadraticMap.sq (R := F)).comp (LinearMap.fst F F F) +
    b • (QuadraticMap.sq (R := F)).comp (LinearMap.snd F F F)

@[simp] theorem binaryForm_apply (a b : F) (p : F × F) :
    binaryForm a b p = a * p.1 ^ 2 + b * p.2 ^ 2 := by
  simp [binaryForm, QuadraticMap.sq, QuadraticMap.linMulLin_apply, pow_two]

/-- The basis with first vector (x,y), second (-by,ax), has determinant one. -/
def binaryNormalizationLinear (a b x y : F) (h : a * x ^ 2 + b * y ^ 2 = 1) :
    (F × F) ≃ₗ[F] (F × F) where
  toFun p := (x*p.1-b*y*p.2, y*p.1+a*x*p.2)
  invFun p := (a*x*p.1+b*y*p.2, -y*p.1+x*p.2)
  left_inv p := by
    apply Prod.ext
    · dsimp
      linear_combination p.1 * h
    · dsimp
      linear_combination p.2 * h
  right_inv p := by
    apply Prod.ext
    · dsimp
      linear_combination p.1 * h
    · dsimp
      linear_combination p.2 * h
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' c p := by ext <;> simp [smul_eq_mul] <;> ring

/-- Exact normalization retains the product ab, not just its square class. -/
def binaryNormalizationIsometry (a b x y : F) (h : a * x ^ 2 + b * y ^ 2 = 1) :
    (binaryForm 1 (a*b)).IsometryEquiv (binaryForm a b) where
  toLinearEquiv := binaryNormalizationLinear a b x y h
  map_app' p := by
    change binaryForm a b (x*p.1-b*y*p.2, y*p.1+a*x*p.2) = binaryForm 1 (a*b) p
    simp only [binaryForm_apply, one_mul]
    linear_combination (p.1 ^ 2 + a*b*p.2 ^ 2) * h

/-- Every nondegenerate diagonal binary form over a finite odd field normalizes to <1,ab>. -/
theorem finite_binary_normalization [Finite F] (h2 : (2 : F) ≠ 0)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty ((binaryForm a b).IsometryEquiv (binaryForm 1 (a*b))) := by
  obtain ⟨x,y,h⟩ := Atlas.finite_field_binary_represents h2 a b ha hb 1
  exact ⟨(binaryNormalizationIsometry a b x y h).symm⟩
end Atlas.Quadratic
