import Atlas.LinearGroups.ReeF4.TorusWeights
import Atlas.LinearGroups.ReeF4.MarkedBasis

/-! The source torus as actual linear transformations of the retained Albert
trace kernel. The two dependent diagonal coordinates are fixed, and the 24
root coordinates carry the source characters. No group order is used. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def rootDiagonalFormula (d : ShortRootLabel → Fˣ) (w : Carrier F) : Carrier F :=
  (w.1, fun b j => (d (b,j) : F) * w.2 b j)

@[simp] theorem rootDiagonalFormula_trace (d : ShortRootLabel → Fˣ) (w : Carrier F) :
    trace (rootDiagonalFormula d w) = trace w := rfl

def rootDiagonalLinear (d : ShortRootLabel → Fˣ) : TraceZero F →ₗ[F] TraceZero F where
  toFun w := ⟨rootDiagonalFormula d w.val, w.property⟩
  map_add' u v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext b j
      exact mul_add _ _ _
  map_smul' a u := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext b j
      simp [rootDiagonalFormula, smul_eq_mul, mul_left_comm]

private theorem rootDiagonalLinear_inverse (d : ShortRootLabel → Fˣ) (w : TraceZero F) :
    rootDiagonalLinear (fun r => (d r)⁻¹) (rootDiagonalLinear d w) = w := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext b j
    change (((d (b,j))⁻¹ : Fˣ) : F) * ((d (b,j) : F) * w.val.2 b j) = w.val.2 b j
    simp [← mul_assoc]

def rootDiagonalEquiv (d : ShortRootLabel → Fˣ) : TraceZero F ≃ₗ[F] TraceZero F where
  __ := rootDiagonalLinear d
  invFun := rootDiagonalLinear (fun r => (d r)⁻¹)
  left_inv := rootDiagonalLinear_inverse d
  right_inv w := by
    have h := rootDiagonalLinear_inverse (fun r => (d r)⁻¹) w
    have hd : (fun r => ((d r)⁻¹)⁻¹) = d := by funext r; exact inv_inv (d r)
    rw [hd] at h
    exact h

@[simp] theorem rootDiagonalEquiv_apply (d : ShortRootLabel → Fˣ) (w : TraceZero F) :
    rootDiagonalEquiv d w = rootDiagonalLinear d w := rfl

def torusEquiv (m : ℕ) (a b : Fˣ) : TraceZero F ≃ₗ[F] TraceZero F :=
  rootDiagonalEquiv (torusWeight (G := Fˣ) m a b)

@[simp] theorem torusEquiv_diagonal (m : ℕ) (a b : Fˣ) (i : Fin 3) :
    torusEquiv m a b (diagonalVector i) = diagonalVector i := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext j k
    simp [torusEquiv, rootDiagonalEquiv, rootDiagonalLinear, rootDiagonalFormula,
      diagonalVector, traceZeroProjection, unit]

@[simp] theorem torusEquiv_root (m : ℕ) (a b : Fˣ) (r : ShortRootLabel) :
    torusEquiv m a b (rootVector r) = (torusWeight (G := Fˣ) m a b r : F) • rootVector r := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    simp [torusEquiv, rootDiagonalEquiv, rootDiagonalLinear, rootDiagonalFormula, rootVector]
  · funext i j
    by_cases hi : i = r.1 <;> by_cases hj : j = r.2 <;>
      simp [torusEquiv, rootDiagonalEquiv, rootDiagonalLinear, rootDiagonalFormula,
        rootVector, Pi.single_apply, hi, hj, smul_eq_mul]

end Atlas.ReeF4
