import Atlas.LinearAlgebra.QuadraticBinaryNormalization
import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-! # Finite odd-field normalization of diagonal quadratic forms -/
noncomputable section
namespace Atlas.Quadratic
variable {F : Type*} [Field F]

abbrev diagonalForm {n : ℕ} (w : Fin n → F) : QuadraticForm F (Fin n → F) :=
  QuadraticMap.weightedSumSquares F w

def splitFirstTwo (n : ℕ) : (Fin (n + 2) → F) ≃ₗ[F] (F × F) × (Fin n → F) where
  toFun v := ((v 0, v 1), fun i => v i.succ.succ)
  invFun p := Fin.cons p.1.1 (Fin.cons p.1.2 p.2)
  left_inv v := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
  right_inv p := by rfl
  map_add' v w := rfl
  map_smul' c v := rfl

/-- Splitting off the first two coordinates identifies their actual binary form. -/
def diagonalSplitTwo {n : ℕ} (a b : F) (w : Fin n → F) :
    (diagonalForm (Fin.cons a (Fin.cons b w))).IsometryEquiv
      ((binaryForm a b).prod (diagonalForm w)) where
  toLinearEquiv := splitFirstTwo n
  map_app' v := by
    simp [QuadraticMap.prod_apply, diagonalForm, QuadraticMap.weightedSumSquares_apply,
      splitFirstTwo, Fin.sum_univ_succ, binaryForm_apply, pow_two, add_assoc]

/-- Any binary isometry acts on the first two coordinates and fixes all others. -/
def diagonalChangeTwo {n : ℕ} {a b c d : F} (w : Fin n → F)
    (e : (binaryForm a b).IsometryEquiv (binaryForm c d)) :
    (diagonalForm (Fin.cons a (Fin.cons b w))).IsometryEquiv
      (diagonalForm (Fin.cons c (Fin.cons d w))) :=
  (diagonalSplitTwo a b w).trans
    ((e.prod (QuadraticMap.IsometryEquiv.refl (diagonalForm w))).trans
      (diagonalSplitTwo c d w).symm)

/-- Appending a common first coefficient preserves a diagonal isometry. -/
def diagonalCons {n : ℕ} (a : F) {w z : Fin n → F}
    (e : (diagonalForm w).IsometryEquiv (diagonalForm z)) :
    (diagonalForm (Fin.cons a w)).IsometryEquiv (diagonalForm (Fin.cons a z)) where
  toFun v := Fin.cons (v 0) (e (fun i => v i.succ))
  invFun v := Fin.cons (v 0) (e.symm (fun i => v i.succ))
  left_inv v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa using congrFun (e.symm_apply_apply (fun i => v i.succ)) j
  right_inv v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa using congrFun (e.apply_symm_apply (fun i => v i.succ)) j
  map_add' v t := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change e.toLinearEquiv ((fun i => v i.succ) + (fun i => t i.succ)) j =
        (e.toLinearEquiv (fun i => v i.succ) + e.toLinearEquiv (fun i => t i.succ)) j
      exact congrFun (e.toLinearEquiv.map_add _ _) j
  map_smul' c v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change e.toLinearEquiv (c • (fun i => v i.succ)) j =
        (c • e.toLinearEquiv (fun i => v i.succ)) j
      exact congrFun (e.toLinearEquiv.map_smul c _) j
  map_app' v := by
    have h := e.map_app (fun i => v i.succ)
    simp only [diagonalForm, QuadraticMap.weightedSumSquares_apply,
      Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_eq_mul] at h ⊢
    exact congrArg (fun t => a * (v 0 * v 0) + t) h

/-- Normalized coefficients: all ones followed by the retained final coefficient. -/
def normalWeights : (n : ℕ) → F → (Fin (n + 1) → F)
  | 0, d => fun _ => d
  | n + 1, d => Fin.cons 1 (normalWeights n d)

/-- Actual diagonal normalization to ones and the exact product of the original coefficients. -/
theorem finite_diagonal_normalization [Finite F] (h2 : (2 : F) ≠ 0)
    (n : ℕ) (w : Fin (n + 1) → F) (hw : ∀ i, w i ≠ 0) :
    Nonempty ((diagonalForm w).IsometryEquiv
      (diagonalForm (normalWeights n (∏ i, w i)))) := by
  induction n with
  | zero =>
    have he : w = normalWeights 0 (∏ i, w i) := by
      funext i
      fin_cases i
      simp [normalWeights]
    exact ⟨QuadraticForm.weightedSumSquaresCongr he⟩
  | succ n ih =>
    let v : Fin (n + 1) → F := Fin.cons (w 0 * w 1) (fun i => w i.succ.succ)
    have hv : ∀ i, v i ≠ 0 := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact mul_ne_zero (hw 0) (hw 1)
      · exact hw j.succ.succ
    obtain ⟨e⟩ := finite_binary_normalization h2 (w 0) (w 1) (hw 0) (hw 1)
    obtain ⟨f⟩ := ih v hv
    have heq : Fin.cons (w 0) (Fin.cons (w 1) (fun i : Fin n => w i.succ.succ)) = w := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
    have hp : (∏ i, v i) = ∏ i, w i := by
      simp [v, Fin.prod_univ_succ, mul_assoc]
    have e' := (diagonalChangeTwo (fun i : Fin n => w i.succ.succ) e).trans (diagonalCons 1 f)
    rw [heq] at e'
    simpa only [normalWeights, hp] using Nonempty.intro e'

/-- Rescaling only the final coordinate realizes the square-class ambiguity. -/
def normalWeightsSquareEquiv (n : ℕ) (d e : F) (u : Fˣ)
    (h : e * (u : F) ^ 2 = d) :
    (diagonalForm (normalWeights n d)).IsometryEquiv
      (diagonalForm (normalWeights n e)) := by
  induction n with
  | zero =>
    exact QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares
      (fun _ => u) (fun _ => h)
  | succ n ih => exact diagonalCons 1 ih

/-- Diagonal nondegenerate forms of the same positive dimension and square-equivalent
products have an actual isometry. -/
theorem finite_diagonal_isometry_of_product_square [Finite F] (h2 : (2 : F) ≠ 0)
    (n : ℕ) (w z : Fin (n + 1) → F) (hw : ∀ i, w i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (c : F) (hc : (∏ i, z i) * c ^ 2 = ∏ i, w i) :
    Nonempty ((diagonalForm w).IsometryEquiv (diagonalForm z)) := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 2 ≠ 0), mul_zero] at hc
    exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)) hc.symm
  obtain ⟨e⟩ := finite_diagonal_normalization h2 n w hw
  obtain ⟨f⟩ := finite_diagonal_normalization h2 n z hz
  let u := Units.mk0 c hc0
  exact ⟨e.trans ((normalWeightsSquareEquiv n (∏ i, w i) (∏ i, z i) u hc).trans f.symm)⟩

/-- The finite-field discriminant square class suffices for diagonal isometry. -/
theorem finite_diagonal_isometry_of_square_ratio [Finite F] (h2 : (2 : F) ≠ 0)
    (n : ℕ) (w z : Fin (n + 1) → F) (hw : ∀ i, w i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hs : IsSquare ((∏ i, w i) / ∏ i, z i)) :
    Nonempty ((diagonalForm w).IsometryEquiv (diagonalForm z)) := by
  obtain ⟨c,hc⟩ := hs
  have hz0 : (∏ i, z i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hz i)
  apply finite_diagonal_isometry_of_product_square h2 n w z hw hz c
  rw [← pow_two] at hc
  have h := (div_eq_iff hz0).mp hc
  simpa only [mul_comm] using h.symm

/-- Unit coefficients agree with their underlying field coefficients as actual forms. -/
theorem weighted_units_eq_diagonal {n : ℕ} (w : Fin n → Fˣ) :
    QuadraticMap.weightedSumSquares F w = diagonalForm (fun i => (w i : F)) := by
  ext v
  simp only [diagonalForm, QuadraticMap.weightedSumSquares_apply, Units.smul_def, smul_eq_mul]

/-- The normalization interface directly accepts the unit coefficients produced by diagonalization. -/
theorem finite_unit_diagonal_normalization [Finite F] (h2 : (2 : F) ≠ 0)
    (n : ℕ) (w : Fin (n + 1) → Fˣ) :
    Nonempty ((QuadraticMap.weightedSumSquares F w).IsometryEquiv
      (diagonalForm (normalWeights n (∏ i, (w i : F))))) := by
  rw [weighted_units_eq_diagonal]
  exact finite_diagonal_normalization h2 n (fun i => (w i : F)) (fun i => (w i).ne_zero)

/-- Equal dimension and discriminant square class give an isometry of unit-diagonal forms. -/
theorem finite_unit_diagonal_isometry_of_square_ratio [Finite F] (h2 : (2 : F) ≠ 0)
    (n : ℕ) (w z : Fin (n + 1) → Fˣ)
    (hs : IsSquare ((∏ i, (w i : F)) / ∏ i, (z i : F))) :
    Nonempty ((QuadraticMap.weightedSumSquares F w).IsometryEquiv
      (QuadraticMap.weightedSumSquares F z)) := by
  rw [weighted_units_eq_diagonal, weighted_units_eq_diagonal]
  exact finite_diagonal_isometry_of_square_ratio h2 n _ _
    (fun i => (w i).ne_zero) (fun i => (z i).ne_zero) hs
end Atlas.Quadratic


