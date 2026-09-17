import Atlas.Algebra.IcosianOrderBasis
import Atlas.Algebra.IcosianCoordinateNorm
import Mathlib.Algebra.CharP.Two

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Algebra
open Atlas.Codes
open scoped Quaternion QuadraticAlgebra BigOperators

/-- Twice the eight rational coordinates of an integral icosian. -/
def icosianIntegralDouble (a : Fin 4 → GoldenInteger) : IcosianIntegerCoordinates :=
  ![2*(a 0).re+(a 2).re-(a 3).re+(a 3).im,
    2*(a 0).im+(a 2).im+(a 3).re,
    2*(a 1).re+(a 2).re-(a 2).im+(a 3).re,
    2*(a 1).im-(a 2).re+(a 3).im,
    -(a 3).im,-(a 3).re-(a 3).im,(a 2).im,(a 2).re+(a 2).im]

theorem icosianIntegralDouble_synthesis (a : Fin 4 → GoldenInteger) :
    icosianCoordinatesQuaternion (icosianIntegralDouble a)=
      icosianBasisSynthesis (fun i => goldenIntegerToRational (a i)) := by
  ext <;> simp [icosianCoordinatesQuaternion,icosianIntegralDouble,
    icosianBasisSynthesis,goldenIntegerToRational,icosianGenerator,icosianI] <;> ring

theorem icosianIntegralDouble_parity (a : Fin 4 → GoldenInteger) :
    (fun i => (icosianIntegralDouble a i : Bit)) ∈ icosianParity := by
  refine ⟨![(a 2).re,(a 2).im,(a 3).re,(a 3).im],?_⟩
  funext j
  fin_cases j <;> simp [icosianParityEncoder,icosianParityRows,
    icosianIntegralDouble,Fin.sum_univ_succ,CharTwo.sub_eq_add,CharTwo.neg_eq] <;> ring

theorem isIcosian_has_parity_coordinates {x : IcosianQuaternion} (hx : IsIcosian x) :
    ∃ v : IcosianIntegerCoordinates,
      (fun i => (v i : Bit)) ∈ icosianParity ∧ icosianCoordinatesQuaternion v=x := by
  obtain ⟨a,rfl⟩ := (isIcosian_iff_synthesis x).mp hx
  exact ⟨icosianIntegralDouble a,icosianIntegralDouble_parity a,
    icosianIntegralDouble_synthesis a⟩

end Atlas.Algebra
