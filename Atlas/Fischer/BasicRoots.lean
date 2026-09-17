import Atlas.Fischer.AxisSums
import Atlas.Fischer.Roots

namespace Atlas.Fischer
open Atlas.Codes

theorem basicAxis_product (i : Omega) :
    product (basicAxis i) (basicAxis i) = (10 : Scalar) • basicAxis i := by
  classical
  simp only [basicAxis_eq]
  rw [product_sub_left, product_sub_right, product_sub_right,
    product_smul_right, product_smul_left, product_smul_left, product_smul_right,
    product_axisSum_self, product_comm axisSum (u i), product_u_axisSum,
    product_u, axisBasisProduct_normalForm]
  norm_num [smul_smul]
  module

theorem basicAxis_isRoot (i : Omega) : IsRoot (basicAxis i) :=
  ⟨basicAxis_norm i, basicAxis_product i⟩

end Atlas.Fischer
