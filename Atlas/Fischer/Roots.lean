import Atlas.Fischer.CoordinateProduct

namespace Atlas.Fischer

/-- The two source root equations; reflecting roots impose additional conditions later. -/
def IsRoot (r : Coordinates) : Prop := hermitian r r = 9 ∧ product r r = (10 : Scalar) • r

/-- The source conjugate-linear root map, without any involutivity assumption. -/
noncomputable def rootMap (r x : Coordinates) : Coordinates :=
  product x r - hermitian r x • r

theorem rootMap_smul (r x : Coordinates) (a : Scalar) :
    rootMap r (a • x) = star a • rootMap r x := by
  simp only [rootMap, product_smul_left, hermitian_smul_right, smul_sub, smul_smul]

theorem rootMap_phase (r x : Coordinates) (a : Scalar) (ha : a ^ 3 = 1) :
    rootMap (a • r) x = a ^ 2 • rootMap r x := by
  simp only [rootMap, product_smul_right, hermitian_smul_left, cube_root_conjugate ha,
    smul_sub, smul_smul]
  congr 1
  congr 1
  ring

theorem root_phase (r : Coordinates) (hr : IsRoot r) (a : Scalar) (ha : a ^ 3 = 1) :
    IsRoot (a • r) := by
  constructor
  · rw [hermitian_smul_left, hermitian_smul_right, hr.1]
    calc
      a * (star a * 9) = (star a * a) * 9 := by ring
      _ = 9 := by rw [cube_root_unit_norm ha, one_mul]
  · rw [product_smul_left, product_smul_right, hr.2, smul_smul, smul_smul, smul_smul]
    congr 1
    rw [cube_root_conjugate ha]
    calc
      a ^ 2 * a ^ 2 * 10 = a ^ 3 * (10 * a) := by ring
      _ = 10 * a := by rw [ha, one_mul]

end Atlas.Fischer
