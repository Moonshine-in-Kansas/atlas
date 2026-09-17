import Atlas.Fischer.CoordinateProduct

namespace Atlas.Fischer

/-- The source's scalar automorphisms, separate from the Parker standard group. -/
noncomputable def scalarPhaseEquiv (a : Mu3) : Coordinates ≃ₗ[Scalar] Coordinates :=
  LinearEquiv.smulOfUnit a.val

theorem scalarPhaseEquiv_apply (a : Mu3) (x : Coordinates) :
    scalarPhaseEquiv a x = (a.val.val : Scalar) • x := rfl

theorem scalarPhaseEquiv_product (a : Mu3) (x y : Coordinates) :
    product (scalarPhaseEquiv a x) (scalarPhaseEquiv a y) =
      scalarPhaseEquiv a (product x y) := by
  simp only [scalarPhaseEquiv_apply, product_smul_left, product_smul_right, smul_smul]
  have hc : (a.val.val : Scalar) ^ 3 = 1 := (mem_rootsOfUnity' _ _).mp a.prop
  have he : star (a.val.val : Scalar) * star a.val.val = a.val.val := by
    rw [cube_root_conjugate hc]
    calc
      a.val.val ^ 2 * a.val.val ^ 2 = a.val.val ^ 3 * a.val.val := by ring
      _ = a.val.val := by rw [hc, one_mul]
  rw [he]

theorem scalarPhaseEquiv_hermitian (a : Mu3) (x y : Coordinates) :
    hermitian (scalarPhaseEquiv a x) (scalarPhaseEquiv a y) = hermitian x y := by
  simp only [scalarPhaseEquiv_apply, hermitian_smul_left, hermitian_smul_right]
  have hc : (a.val.val : Scalar) ^ 3 = 1 := (mem_rootsOfUnity' _ _).mp a.prop
  calc
    star a.val.val * (a.val.val * hermitian x y) =
      (star a.val.val * a.val.val) * hermitian x y := by ring
    _ = _ := by rw [cube_root_unit_norm hc, one_mul]

end Atlas.Fischer
