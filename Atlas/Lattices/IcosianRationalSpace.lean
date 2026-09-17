import Atlas.Algebra.IcosianQuaternion
import Atlas.Lattices.LeechForm

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators Quaternion QuadraticAlgebra Matrix

abbrev IcosianRationalCoordinates := Fin 3 → IcosianQuaternion
abbrev IcosianRealIndex := Fin 3 × (Fin 4 × Fin 2)

def icosianHermitian (x y : IcosianRationalCoordinates) : IcosianQuaternion :=
  (1/2 : ℚ) • ∑ i, star (x i) * y i

def icosianBilinear (x y : IcosianRationalCoordinates) : ℚ :=
  2 * icosianFunctional (icosianHermitian x y)

def icosianQuaternionCoordinate (x : IcosianQuaternion) (i : Fin 4) : GoldenRational :=
  ![x.re,x.imI,x.imJ,x.imK] i

def icosianRealCoordinates :
    IcosianRationalCoordinates ≃ₗ[ℚ] (IcosianRealIndex → ℚ) where
  toFun z p := if p.2.2=0 then (icosianQuaternionCoordinate (z p.1) p.2.1).re
    else (icosianQuaternionCoordinate (z p.1) p.2.1).im
  invFun x i := ⟨⟨x (i,0,0),x (i,0,1)⟩,⟨x (i,1,0),x (i,1,1)⟩,
    ⟨x (i,2,0),x (i,2,1)⟩,⟨x (i,3,0),x (i,3,1)⟩⟩
  left_inv z := by funext i; ext <;> simp [icosianQuaternionCoordinate]
  right_inv x := by
    funext ⟨i,j,k⟩
    fin_cases j <;> fin_cases k <;> simp [icosianQuaternionCoordinate]
  map_add' z w := by
    funext ⟨i,j,k⟩
    fin_cases j <;> fin_cases k <;> simp [icosianQuaternionCoordinate]
  map_smul' r z := by
    funext ⟨i,j,k⟩
    fin_cases j <;> fin_cases k <;> simp [icosianQuaternionCoordinate]

theorem icosianBilinear_eq_dot (z w : IcosianRationalCoordinates) :
    icosianBilinear z w = dotProduct (icosianRealCoordinates z) (icosianRealCoordinates w) := by
  simp [icosianBilinear,icosianHermitian,icosianFunctional,goldenFunctional,
    Quaternion.re_mul,icosianRealCoordinates,icosianQuaternionCoordinate,dotProduct,
    Fintype.sum_prod_type,Fin.sum_univ_succ,Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

end Atlas.Lattices
