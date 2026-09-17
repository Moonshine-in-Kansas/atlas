import Atlas.Lattices.IcosianComparisonGeneratorsData
import Atlas.Algebra.IcosianModuloTwoKernel

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators QuadraticAlgebra
attribute [local irreducible] icosianIntegralCoefficients icosianIntegralSynthesis

theorem icosianSourceGenerator_coefficients (n : Fin 36) (i : Fin 3) :
    icosianIntegralLinearEquiv (icosianComparisonSourceGenerator n i)=
      icosianComparisonSourceCoefficients n i :=
  icosianIntegralEquiv.apply_symm_apply _

theorem icosianEven_mem_of_generators (S : Submodule ℤ IcosianCoordinates)
    (hS : ∀ n : Fin 24,icosianComparisonSourceGenerator ⟨n.val,by omega⟩ ∈ S)
    (x : IcosianCoordinates)
    (hx : ∀ i j,goldenModuloTwo (icosianIntegralCoefficients (x i) j)=0) : x ∈ S := by
  let c : IcosianRealIndex → ℤ := fun p =>
    if p.2.2=0 then (icosianIntegralCoefficients (x p.1) p.2.1).re/2
    else (icosianIntegralCoefficients (x p.1) p.2.1).im/2
  let g : IcosianRealIndex → IcosianCoordinates := fun p =>
    icosianComparisonSourceGenerator ⟨(icosianRealCoordinateIndex p).val,by
      have := (icosianRealCoordinateIndex p).isLt; omega⟩
  have he : (∑ p,c p • g p)=x := by
    funext i
    apply icosianIntegralLinearEquiv.injective
    simp only [Finset.sum_apply,Pi.smul_apply,map_sum,map_smul]
    funext j
    have hr := Int.ediv_mul_cancel ((goldenModuloTwo_eq_zero _).mp (hx i j)).1
    have hi := Int.ediv_mul_cancel ((goldenModuloTwo_eq_zero _).mp (hx i j)).2
    simp only [g,icosianSourceGenerator_coefficients]
    fin_cases i <;> fin_cases j <;> ext <;>
      simp [c,icosianComparisonSourceCoefficients,icosianComparisonSourceData,
        icosianRealCoordinateIndex,Fintype.sum_prod_type,Fin.sum_univ_succ] <;>
      first | exact hr | exact hi
  rw [← he]
  exact S.sum_mem fun p _ => S.smul_mem (c p) (hS (icosianRealCoordinateIndex p))

end Atlas.Lattices
