import Atlas.Fischer.WeightedCubicTensor
import Atlas.Fischer.ComplexCoordinateExtension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Basis.SMul

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The source's actual complex normalization: sqrt(8) on points and 1 on octads. -/
def cubicMetricScale : CoordinateIndex → ℂ
  | .inl _ => (Real.sqrt 8 : ℝ)
  | .inr _ => 1

theorem cubicMetricScale_star (i : CoordinateIndex) : star (cubicMetricScale i) = cubicMetricScale i := by
  cases i <;> simp [cubicMetricScale]

theorem cubicMetricScale_sq (i : CoordinateIndex) :
    cubicMetricScale i ^ 2 = scalarToComplex (inverseCoordinateMetric i) := by
  cases i
  · simp only [cubicMetricScale, inverseCoordinateMetric, coordinateWeight, map_inv₀, map_div₀,
      map_one, map_ofNat]
    norm_num [← Complex.ofReal_pow, Real.sq_sqrt, map_ofNat, map_natCast]
  · simp [cubicMetricScale, inverseCoordinateMetric, coordinateWeight]

theorem cubicMetricScale_ne_zero (i : CoordinateIndex) : cubicMetricScale i ≠ 0 := by
  intro h
  have hs := cubicMetricScale_sq i
  rw [h, zero_pow (by decide)] at hs
  have hn : scalarToComplex (inverseCoordinateMetric i) ≠ 0 := by
    apply (map_ne_zero scalarToComplex).mpr
    exact inv_ne_zero (coordinateMetric_ne_zero i)
  exact hn hs.symm

def complexCoordinateHermitian (x y : CoordinateIndex → ℂ) : ℂ :=
  ∑ i, (coordinateWeight i : ℂ) * x i * star (y i)

/-- The complex form extends the retained form, not a separately chosen metric. -/
theorem complexCoordinateHermitian_embedding (x y : Coordinates) :
    complexCoordinateHermitian (fun i => scalarToComplex (x i)) (fun i => scalarToComplex (y i)) =
      scalarToComplex (hermitian x y) := by
  simp only [complexCoordinateHermitian, hermitian, weightedHermitian, map_sum, map_mul,
    map_ratCast, scalarToComplex_star]

/-- The scaled coordinate vectors form an actual complex basis. -/
def cubicNormalizedBasis : Module.Basis CoordinateIndex ℂ (CoordinateIndex → ℂ) :=
  (Pi.basisFun ℂ CoordinateIndex).unitsSMul (fun i => Units.mk0 (cubicMetricScale i) (cubicMetricScale_ne_zero i))

theorem cubicNormalizedBasis_apply (i : CoordinateIndex) :
    cubicNormalizedBasis i = cubicMetricScale i • Pi.single i (1 : ℂ) := by
  simp [cubicNormalizedBasis, Module.Basis.unitsSMul_apply, Pi.basisFun_apply]

theorem cubicNormalizedBasis_orthonormal (i j : CoordinateIndex) :
    complexCoordinateHermitian (cubicNormalizedBasis i) (cubicNormalizedBasis j) =
      if i = j then 1 else 0 := by
  rw [cubicNormalizedBasis_apply, cubicNormalizedBasis_apply]
  by_cases h : i = j
  · subst j
    simp only [complexCoordinateHermitian, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      star_mul, cubicMetricScale_star]
    simp only [mul_ite, mul_one, mul_zero, apply_ite, star_one, star_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hm : scalarToComplex (inverseCoordinateMetric i) * (coordinateWeight i : ℂ) = 1 := by
      simpa only [map_mul, map_one, map_ratCast] using congrArg scalarToComplex (inverseCoordinateMetric_mul i)
    calc
      _ = cubicMetricScale i ^ 2 * (coordinateWeight i : ℂ) := by ring
      _ = 1 := by rw [cubicMetricScale_sq]; exact hm
  · simp [complexCoordinateHermitian, Pi.single_apply, h, Ne.symm h]

end Atlas.Fischer
