import Atlas.Fischer.OctadicRootMapAxes

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def duadicAxisPart (p : Finset Omega) : Coordinates := axisSum-(8 : Scalar) • ∑ i ∈ p, u i

theorem product_octadAxisSum_duad_pair (F G : Octad) (hFG : (F.val ∩ G.val).card=2) :
    product (octadAxisSum F) (octadAxisSum G)=(-1/4 : Scalar) • axisSum+
      octadAxisSum F+octadAxisSum G-∑ i ∈ F.val ∩ G.val, u i := by
  have hi (i : Omega) : product (u i) (octadAxisSum G)=
      (-1/16 : Scalar) • axisSum+u i+(1/8 : Scalar) • octadAxisSum G+
        (if i ∈ G.val then (1/8 : Scalar) • axisSum-u i else 0) := by
    by_cases h : i ∈ G.val
    · rw [product_u_octadAxisSum_inside G i h,if_pos h]
      module
    · rw [product_u_octadAxisSum_outside G i h,if_neg h]
      module
  rw [octadAxisSum,product_sum_left]
  simp_rw [hi]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_add_distrib,
    Finset.sum_const,Finset.sum_const,octad_size F.val F.property,← Finset.sum_filter,
    Finset.filter_mem_eq_inter,Finset.sum_sub_distrib,Finset.sum_const,hFG]
  change (8 : ℕ) • ((-1/16 : Scalar) • axisSum)+octadAxisSum F+
    (8 : ℕ) • ((1/8 : Scalar) • octadAxisSum G)+
      ((2 : ℕ) • ((1/8 : Scalar) • axisSum)-∑ i ∈ F.val ∩ G.val, u i)=
      (-1/4 : Scalar) • axisSum+octadAxisSum F+octadAxisSum G-∑ i ∈ F.val ∩ G.val, u i
  module

theorem product_octadicAxis_duad_pair (F G : Octad) (hFG : (F.val ∩ G.val).card=2) :
    product (octadicAxisPart F) (octadicAxisPart G)=
      (1/2 : Scalar) • duadicAxisPart (F.val ∩ G.val) := by
  rw [octadicAxisPart_eq,octadicAxisPart_eq,product_sub_left,product_sub_right,
    product_sub_right,product_smul_left,product_smul_left,product_smul_right,
    product_smul_right,product_axisSum_self,product_axisSum_octadAxisSum,
    product_comm (octadAxisSum F) axisSum,product_axisSum_octadAxisSum,
    product_octadAxisSum_duad_pair F G hFG]
  norm_num only [star_ofNat]
  unfold duadicAxisPart
  module

end Atlas.Fischer
