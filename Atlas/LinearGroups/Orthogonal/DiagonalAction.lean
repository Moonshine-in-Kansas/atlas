import Atlas.LinearGroups.Orthogonal.Basic
import Mathlib.Tactic

/-! Diagonal hyperbolic isometries in all characteristics. -/
noncomputable section
namespace Atlas.Orthogonal
variable {K : Type*} [Field K] {n : ℕ}

def diagonalLinear (d : Fin n → Kˣ) : VectorD n K ≃ₗ[K] VectorD n K where
  toFun x := Sum.elim (fun i => (d i : K)*x (.inl i)) (fun i => ((d i)⁻¹ : Kˣ)*x (.inr i))
  invFun x := Sum.elim (fun i => ((d i)⁻¹ : Kˣ)*x (.inl i)) (fun i => (d i : K)*x (.inr i))
  left_inv x := by ext i; rcases i with i|i <;> simp [←mul_assoc]
  right_inv x := by ext i; rcases i with i|i <;> simp [←mul_assoc]
  map_add' x y := by ext i; rcases i with i|i <;> simp [mul_add]
  map_smul' c x := by ext i; rcases i with i|i <;> simp [mul_left_comm]

theorem diagonalLinear_form (d : Fin n → Kˣ) (x : VectorD n K) :
    formD n K (diagonalLinear d x) = formD n K x := by
  simp only [formD_apply, diagonalLinear, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Sum.elim_inl, Sum.elim_inr]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ((d i : K) * ((d i)⁻¹ : Kˣ)) * (x (.inl i)*x (.inr i)) := by ring
    _ = x (.inl i)*x (.inr i) := by simp

def diagonalEmbedding : (Fin n → Kˣ) →* O_DPlus n K where
  toFun d := ⟨diagonalLinear d,diagonalLinear_form d⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    ext i; rcases i with i|i <;> simp [diagonalLinear]
  map_mul' d e := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change diagonalLinear (d*e) x = diagonalLinear d (diagonalLinear e x)
    ext i; rcases i with i|i <;> simp [diagonalLinear, mul_assoc, mul_left_comm]

theorem diagonalEmbedding_injective : Function.Injective (diagonalEmbedding (n:=n) (K:=K)) := by
  intro d e h
  funext i
  apply Units.ext
  have he := congrArg (fun g : O_DPlus n K => g.val (Pi.single (.inl i) 1) (.inl i)) h
  simpa [diagonalEmbedding, diagonalLinear] using he

end Atlas.Orthogonal
