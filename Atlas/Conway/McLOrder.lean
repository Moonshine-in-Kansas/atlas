import Atlas.Conway.McLEndpointSequence

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open Atlas.Sporadic.Conway3
attribute [local instance] Classical.propDecidable

theorem mcl_endpoints_card : Nat.card McLEndpoints = 2 := by
  simp [McLEndpoints,Nat.card_eq_fintype_card,mcl_endpoints_ne]

theorem mcl_endpoint_permutation_card : Nat.card (Equiv.Perm McLEndpoints) = 2 := by
  rw [Nat.card_perm,mcl_endpoints_card]; rfl

theorem mcl_pair_order : Nat.card McLPairStabilizer = 1796256000 := point_stabilizer_card

theorem mcl_endpoint_index_product : 2*Nat.card McLModel = Nat.card McLPairStabilizer := by
  have hk := Nat.card_congr mclEndpointKernelEquiv.toEquiv
  have h := mclEndpointPermutation.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr mcl_endpoint_permutation_surjective,
    Subgroup.card_top,mcl_endpoint_permutation_card,hk] at h
  simpa only [mul_comm] using h

theorem mcl_order : Nat.card McLModel = 898128000 := by
  have h := mcl_endpoint_index_product
  rw [mcl_pair_order] at h
  omega

theorem mcl_order_factorization : Nat.card McLModel = 2^7*3^6*5^3*7*11 := by
  rw [mcl_order]
  norm_num

theorem mcl_co3_index_product : 552*Nat.card McLModel = Nat.card Model := by
  rw [mcl_order,card]; rfl

theorem mcl_pair_co3_index_product : 276*Nat.card McLPairStabilizer = Nat.card Model := by
  rw [mcl_pair_order,card]; rfl

end Atlas.Conway
