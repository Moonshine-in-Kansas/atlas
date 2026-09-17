import Atlas.Algebra.IcosianIntegralCoordinates

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped QuadraticAlgebra Quaternion
attribute [local irreducible] icosianBasisCoefficients goldenIntegerToRational

theorem icosianIntegralCoefficients_mul (x y : icosianOrder) :
    icosianIntegralCoefficients (x*y)=icosianCoefficientProduct
      (QuadraticAlgebra.omega : GoldenInteger)
      (icosianIntegralCoefficients x) (icosianIntegralCoefficients y) := by
  funext i
  apply goldenIntegerToRational_injective
  rw [icosianIntegralCoefficients_spec]
  change icosianBasisCoefficients (x.val*y.val) i=_
  rw [icosianBasisCoefficients_mul]
  have ht : goldenIntegerToRational (QuadraticAlgebra.omega : GoldenInteger)=goldenTau := by unfold goldenIntegerToRational goldenTau; rfl
  fin_cases i <;> simp [icosianCoefficientProduct,ht,icosianIntegralCoefficients_spec]

theorem icosianIntegralCoefficients_one :
    icosianIntegralCoefficients (1 : icosianOrder)=![1,0,0,0] := by
  funext i
  apply goldenIntegerToRational_injective
  rw [icosianIntegralCoefficients_spec]
  change icosianBasisCoefficients (1 : IcosianQuaternion) i=_
  fin_cases i <;> simp [icosianBasisCoefficients]

end Atlas.Algebra
