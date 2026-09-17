import Atlas.Algebra.IcosianIntegralNorm
import Atlas.Algebra.IcosianModuloTwo
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped QuadraticAlgebra Matrix

/-- The full matrix determinant agrees with reduction of the integral reduced norm. -/
theorem icosianMatrixFromCoefficients_det (a : Fin 4 → GoldenFour) :
    Matrix.det (icosianMatrixFromCoefficients a)=icosianCoefficientNorm goldenFourTau a := by
  rw [Matrix.det_fin_two]
  ext <;> simp [icosianMatrixFromCoefficients,icosianCoefficientNorm,
    goldenFourTau,QuadraticAlgebra.omega,pow_two] <;>
    (try simp only [CharTwo.sub_eq_add,CharTwo.neg_eq]) <;> ring_nf <;>
    simp only [(show (2 : ZMod 2)=0 from rfl),(show (3 : ZMod 2)=1 from rfl),
      (show (4 : ZMod 2)=0 from rfl),(show (5 : ZMod 2)=1 from rfl),
      (show (10 : ZMod 2)=0 from rfl),(show (8 : ZMod 2)=0 from rfl),(show (6 : ZMod 2)=0 from rfl),(show (7 : ZMod 2)=1 from rfl),
      mul_zero,mul_one,add_zero,zero_add] <;> ring

theorem icosianModuloTwo_det (x : icosianOrder) :
    Matrix.det (icosianModuloTwo x)=goldenModuloTwo (icosianIntegralNorm x) := by
  change Matrix.det (icosianMatrixFromCoefficients _)=_
  rw [icosianMatrixFromCoefficients_det]
  have ht : goldenModuloTwo (QuadraticAlgebra.omega : GoldenInteger)=goldenFourTau := rfl
  simp [icosianReducedCoefficients,icosianIntegralNorm,icosianCoefficientNorm,ht]

end Atlas.Algebra
