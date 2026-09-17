import Atlas.Algebra.BinaryQuadraticContraction
import Atlas.Algebra.BinaryQuadraticPfaffian

noncomputable section
namespace Atlas.Algebra
open Atlas.Codes
open scoped BigOperators

/-- The actual contraction for an arbitrary full-polar-rank quadratic word,
including its original constant and affine part. -/
theorem binaryQuadraticWord_polar_contraction (w : binaryQuadraticCode)
    (hr : binaryWalshPolarRank (binaryQuadraticWordForm w)=4) (s t : BinaryFour) :
    (∑ v, w.val v * (binaryQuadraticWordForm w).polarBilin s v *
      (binaryQuadraticWordForm w).polarBilin t v) =
        (binaryQuadraticWordForm w).polarBilin s t := by
  let c := binaryQuadraticCodeEquiv.symm w
  have hc : binaryQuadraticEvaluation c=w.val :=
    congrArg Subtype.val (binaryQuadraticCodeEquiv.apply_symm_apply w)
  have hp : binaryQuadraticPfaffian c=1 := binaryQuadraticPfaffian_eq_one c hr
  have h := binaryQuadraticEvaluation_polar_contraction c s t
  rw [hp,one_mul] at h
  simp only [← binaryNormalizedQuadratic_polar,hc] at h
  exact h

end Atlas.Algebra
