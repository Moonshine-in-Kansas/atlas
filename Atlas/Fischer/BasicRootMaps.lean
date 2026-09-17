import Atlas.Fischer.BasicRoots
import Atlas.Fischer.RootRigidity

namespace Atlas.Fischer
open Atlas.Codes

theorem hermitian_basicAxis_u (i j : Omega) :
    hermitian (basicAxis i) (u j) = if j = i then (-7 / 8 : Scalar) else 1 / 8 := by
  rw [← hermitian_star (u j) (basicAxis i)]
  change star (hermitian (coordinateVector (Sum.inl j)) (basicAxis i)) = _
  rw [hermitian_coordinateVector_left]
  by_cases h : j = i <;> norm_num [coordinateWeight, basicAxis, h]

theorem product_u_basicAxis (i j : Omega) :
    product (u j) (basicAxis i) = u j +
      (if j = i then (-7 / 8 : Scalar) else 1 / 8) • basicAxis i := by
  classical
  simp only [basicAxis_eq]
  rw [product_sub_right, product_smul_right, product_u_axisSum,
    product_u, axisBasisProduct_normalForm]
  by_cases h : j = i
  · subst j
    norm_num [smul_smul]
    module
  · norm_num [h, smul_smul]
    module

theorem rootMap_basicAxis_u (i j : Omega) : rootMap (basicAxis i) (u j) = u j := by
  rw [rootMap, product_u_basicAxis, hermitian_basicAxis_u]
  abel

theorem axisOctadBasisProduct_total (O : Octad) :
    (∑ i, axisOctadBasisProduct i O) = (1 / 2 : Scalar) • xOctad O := by
  classical
  have hf : Finset.univ.filter (fun i : Omega => i ∈ O.val) = O.val := by ext i; simp
  have hg : Finset.univ.filter (fun i : Omega => i ∉ O.val) = O.valᶜ := by ext i; simp
  simp only [axisOctadBasisProduct, ← Finset.sum_smul]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, hf, hg, Finset.card_compl, Finset.card_univ]
  rw [octad_size O.val O.prop]
  norm_num [Omega, HexIndex, Tetrad]

theorem product_xOctad_axisSum (O : Octad) :
    product (xOctad O) axisSum = (1 / 2 : Scalar) • xOctad O := by
  rw [axisSum, product_sum_right]
  simp only [product_xOctad_u]
  exact axisOctadBasisProduct_total O

theorem hermitian_basicAxis_xOctad (i : Omega) (O : Octad) :
    hermitian (basicAxis i) (xOctad O) = 0 := by
  rw [← hermitian_star (xOctad O) (basicAxis i)]
  change star (hermitian (coordinateVector (Sum.inr O)) (basicAxis i)) = _
  rw [hermitian_coordinateVector_left]
  simp [basicAxis]

theorem rootMap_basicAxis_xOctad (i : Omega) (O : Octad) :
    rootMap (basicAxis i) (xOctad O) = if i ∈ O.val then -xOctad O else xOctad O := by
  classical
  rw [rootMap, hermitian_basicAxis_xOctad, zero_smul, sub_zero,
    basicAxis_eq, product_sub_right, product_smul_right,
    product_xOctad_axisSum, product_xOctad_u]
  by_cases h : i ∈ O.val <;> norm_num [axisOctadBasisProduct, h, smul_smul] <;> module

end Atlas.Fischer
