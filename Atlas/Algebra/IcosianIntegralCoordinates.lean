import Atlas.Algebra.IcosianOrderBasis
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

def icosianIntegralCoefficients (x : icosianOrder) (i : Fin 4) : GoldenInteger :=
  Classical.choose (x.property i)

theorem icosianIntegralCoefficients_spec (x : icosianOrder) (i : Fin 4) :
    goldenIntegerToRational (icosianIntegralCoefficients x i)=icosianBasisCoefficients x.val i :=
  Classical.choose_spec (x.property i)

def icosianIntegralSynthesis (a : Fin 4 → GoldenInteger) : icosianOrder :=
  ⟨icosianBasisSynthesis (fun i => goldenIntegerToRational (a i)),
    (isIcosian_iff_synthesis _).mpr ⟨a,rfl⟩⟩

attribute [local irreducible] icosianBasisSynthesis icosianBasisCoefficients goldenIntegerToRational

def icosianIntegralEquiv : icosianOrder ≃+ (Fin 4 → GoldenInteger) where
  toFun := icosianIntegralCoefficients
  invFun := icosianIntegralSynthesis
  left_inv x := by
    apply Subtype.ext
    change icosianBasisSynthesis (fun i => goldenIntegerToRational (icosianIntegralCoefficients x i))=x.val
    have h : (fun i => goldenIntegerToRational (icosianIntegralCoefficients x i))=
        icosianBasisCoefficients x.val := funext (icosianIntegralCoefficients_spec x)
    rw [h,icosianBasisSynthesis_coefficients]
  right_inv a := by
    funext i
    apply goldenIntegerToRational_injective
    rw [icosianIntegralCoefficients_spec]
    exact congrFun (icosianBasisCoefficients_synthesis _) i
  map_add' x y := by
    funext i
    apply goldenIntegerToRational_injective
    simp only [Pi.add_apply, map_add,icosianIntegralCoefficients_spec,icosianIntegralCoefficients_spec,
      icosianIntegralCoefficients_spec]
    exact congrFun (icosianBasisCoefficients_add x.val y.val) i

def icosianIntegralLinearEquiv : icosianOrder ≃ₗ[ℤ] (Fin 4 → GoldenInteger) :=
  icosianIntegralEquiv.toIntLinearEquiv

instance icosianOrder_free : Module.Free ℤ icosianOrder :=
  Module.Free.of_equiv icosianIntegralLinearEquiv.symm

instance icosianOrder_finite : Module.Finite ℤ icosianOrder :=
  Module.Finite.equiv icosianIntegralLinearEquiv.symm

theorem icosianOrder_rank : Module.finrank ℤ icosianOrder=8 := by
  rw [icosianIntegralLinearEquiv.finrank_eq,Module.finrank_pi_fintype]
  simp [QuadraticAlgebra.finrank_eq_two]

end Atlas.Algebra
