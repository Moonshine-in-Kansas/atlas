import Atlas.Algebra.IcosianIntegralCoordinates
import Mathlib.Algebra.Module.TransferInstance

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

instance icosianOrder_goldenModule : Module GoldenInteger icosianOrder :=
  icosianIntegralEquiv.module GoldenInteger

def icosianGoldenLinearEquiv : icosianOrder ≃ₗ[GoldenInteger] (Fin 4 → GoldenInteger) :=
  icosianIntegralEquiv.linearEquiv GoldenInteger

instance icosianOrder_goldenFree : Module.Free GoldenInteger icosianOrder :=
  Module.Free.of_equiv icosianGoldenLinearEquiv.symm

instance icosianOrder_goldenFinite : Module.Finite GoldenInteger icosianOrder :=
  Module.Finite.equiv icosianGoldenLinearEquiv.symm

theorem icosianOrder_goldenRank : Module.finrank GoldenInteger icosianOrder=4 := by
  rw [icosianGoldenLinearEquiv.finrank_eq,Module.finrank_pi]
  simp

theorem icosianBasisCoefficients_smul (a : GoldenRational) (x : IcosianQuaternion) :
    icosianBasisCoefficients (a • x)=a • icosianBasisCoefficients x := by
  funext i
  fin_cases i <;> simp [icosianBasisCoefficients] <;> ring

/-- The transported golden-integral module action is the actual central scalar multiplication. -/
theorem icosianOrder_golden_smul (a : GoldenInteger) (x : icosianOrder) :
    (a • x).val=goldenIntegerToRational a • x.val := by
  apply icosianBasisEquiv.injective
  change icosianBasisCoefficients (a • x).val=icosianBasisCoefficients _
  rw [icosianBasisCoefficients_smul]
  funext i
  rw [← icosianIntegralCoefficients_spec]
  have h := congrFun (icosianGoldenLinearEquiv.map_smul a x) i
  change icosianIntegralCoefficients (a • x) i=a*icosianIntegralCoefficients x i at h
  rw [h,map_mul,icosianIntegralCoefficients_spec]
  rfl

end Atlas.Algebra
