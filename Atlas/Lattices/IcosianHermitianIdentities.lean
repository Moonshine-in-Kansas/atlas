import Atlas.Lattices.IcosianRationalSpace

namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators Quaternion

def icosianRightMul (x : IcosianRationalCoordinates) (a : IcosianQuaternion) :
    IcosianRationalCoordinates := fun i => x i*a

@[simp] theorem icosianHermitian_add_left (x y z : IcosianRationalCoordinates) :
    icosianHermitian (x+y) z=icosianHermitian x z+icosianHermitian y z := by
  simp [icosianHermitian,star_add,add_mul,Finset.sum_add_distrib,smul_add]

@[simp] theorem icosianHermitian_add_right (x y z : IcosianRationalCoordinates) :
    icosianHermitian x (y+z)=icosianHermitian x y+icosianHermitian x z := by
  simp [icosianHermitian,mul_add,Finset.sum_add_distrib,smul_add]

@[simp] theorem icosianHermitian_sub_left (x y z : IcosianRationalCoordinates) :
    icosianHermitian (x-y) z=icosianHermitian x z-icosianHermitian y z := by
  simp [icosianHermitian,star_sub,sub_mul,Finset.sum_sub_distrib,smul_sub]

@[simp] theorem icosianHermitian_sub_right (x y z : IcosianRationalCoordinates) :
    icosianHermitian x (y-z)=icosianHermitian x y-icosianHermitian x z := by
  simp [icosianHermitian,mul_sub,Finset.sum_sub_distrib,smul_sub]

@[simp] theorem icosianHermitian_rightMul_right (x y : IcosianRationalCoordinates)
    (a : IcosianQuaternion) :
    icosianHermitian x (icosianRightMul y a)=icosianHermitian x y*a := by
  unfold icosianHermitian icosianRightMul
  rw [smul_mul_assoc]
  congr 1
  simp [Finset.sum_mul,mul_assoc]

@[simp] theorem icosianHermitian_rightMul_left (x y : IcosianRationalCoordinates)
    (a : IcosianQuaternion) :
    icosianHermitian (icosianRightMul x a) y=star a*icosianHermitian x y := by
  simp [icosianHermitian,icosianRightMul,star_mul,mul_assoc,← Finset.mul_sum,
    mul_smul_comm]

theorem icosianHermitian_star (x y : IcosianRationalCoordinates) :
    star (icosianHermitian x y)=icosianHermitian y x := by
  simp [icosianHermitian,star_smul,star_sum,star_mul]

@[simp] theorem icosianHermitian_smul_right (a : ℚ) (x y : IcosianRationalCoordinates) :
    icosianHermitian x (a • y)=a • icosianHermitian x y := by
  simp only [icosianHermitian,Pi.smul_apply,mul_smul_comm,← Finset.smul_sum]
  exact smul_comm _ _ _

end Atlas.Lattices
