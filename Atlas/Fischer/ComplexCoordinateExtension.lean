import Atlas.Fischer.RealCoordinateSpace
import Mathlib.Analysis.Complex.Basic

noncomputable section
namespace Atlas.Fischer

theorem complexTheta_re : (scalarToComplex theta).re = 0 := by
  have h := congrArg Complex.re (scalarToComplex_star theta)
  rw [theta_conjugate, map_neg] at h
  simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at h
  linarith

theorem complexTheta_im_ne_zero : (scalarToComplex theta).im ≠ 0 := by
  intro h
  have hz : scalarToComplex theta = 0 := Complex.ext complexTheta_re h
  have ht : theta = 0 := scalarToComplex_injective (hz.trans (map_zero scalarToComplex).symm)
  have hs := theta_sq
  rw [ht, zero_pow (by decide)] at hs
  norm_num at hs

/-- Complex coordinates in the actual real directions 1 and the embedded theta. -/
def complexThetaRealEquiv : ℂ ≃ₗ[ℝ] ℝ × ℝ where
  toFun z := (z.re, z.im / (scalarToComplex theta).im)
  invFun p := ⟨p.1, p.2 * (scalarToComplex theta).im⟩
  left_inv z := by
    apply Complex.ext
    · rfl
    · exact div_mul_cancel₀ _ complexTheta_im_ne_zero
  right_inv p := by
    apply Prod.ext
    · rfl
    · exact mul_div_cancel_right₀ _ complexTheta_im_ne_zero
  map_add' z w := by
    apply Prod.ext
    · rfl
    · exact add_div _ _ _
  map_smul' a z := by
    apply Prod.ext
    · simp
    · simp
      ring

def complexThetaFunEquiv : ℂ ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  complexThetaRealEquiv.trans (LinearEquiv.finTwoArrow ℝ ℝ).symm

/-- The complex coordinate model, viewed over the reals, with retained coordinate labels. -/
def complexCoordinatesRealEquiv : (CoordinateIndex → ℂ) ≃ₗ[ℝ]
    (RationalCoordinateIndex → ℝ) where
  toFun x p := complexThetaFunEquiv (x p.1) p.2
  invFun f i := complexThetaFunEquiv.symm (fun j => f (i, j))
  left_inv x := by funext i; exact complexThetaFunEquiv.symm_apply_apply (x i)
  right_inv f := by
    funext p
    exact congrFun (complexThetaFunEquiv.apply_symm_apply (fun j => f (p.1, j))) p.2
  map_add' x y := by
    funext p
    exact congrFun (map_add complexThetaFunEquiv (x p.1) (y p.1)) p.2
  map_smul' a x := by
    funext p
    exact congrFun (map_smul complexThetaFunEquiv a (x p.1)) p.2

/-- An explicit real-linear identification with the actual complex coordinate space. -/
def realToComplexCoordinates : RealCoordinates ≃ₗ[ℝ] (CoordinateIndex → ℂ) :=
  realCoordinateEquiv.trans complexCoordinatesRealEquiv.symm

theorem complexThetaRealEquiv_scalar (z : Scalar) :
    complexThetaRealEquiv (scalarToComplex z) =
      (((scalarRealThetaEquiv z).1 : ℝ), ((scalarRealThetaEquiv z).2 : ℝ)) := by
  have h := congrArg scalarToComplex.toLinearMap (scalarRealThetaEquiv_decomposition z)
  rw [map_add, map_smul, map_smul] at h
  change scalarToComplex z = (scalarRealThetaEquiv z).1 • scalarToComplex 1 +
    (scalarRealThetaEquiv z).2 • scalarToComplex theta at h
  rw [map_one] at h
  rw [h]
  apply Prod.ext
  · simp [complexThetaRealEquiv, complexTheta_re]
  · simp [complexThetaRealEquiv, Rat.smul_def, complexTheta_im_ne_zero]

/-- The real-linear identification extends precisely the retained embedding of E into C. -/
theorem realToComplexCoordinates_tmul (a : ℝ) (x : Coordinates) (i : CoordinateIndex) :
    realToComplexCoordinates (a ⊗ₜ[ℚ] x) i = a • scalarToComplex (x i) := by
  apply complexThetaFunEquiv.injective
  funext j
  have hc := congrFun
    (complexCoordinatesRealEquiv.apply_symm_apply
      (realCoordinateEquiv (a ⊗ₜ[ℚ] x))) (i, j)
  change complexThetaFunEquiv (realToComplexCoordinates (a ⊗ₜ[ℚ] x) i) j =
    realCoordinateEquiv (a ⊗ₜ[ℚ] x) (i, j) at hc
  rw [hc, realCoordinateEquiv_tmul, map_smul, Pi.smul_apply]
  fin_cases j <;>
    simp [complexThetaFunEquiv, complexThetaRealEquiv_scalar,
      scalarRealThetaFunEquiv, rationalCoordinateEquiv, mul_comm]

end Atlas.Fischer
