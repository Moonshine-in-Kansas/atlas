import Atlas.Fischer.ResidueQuotientGeneration

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem residueElementary_square (S : Finset Omega) (x : rootGeneratedRayGroup)
    (hx : x ∈ residueElementary S) : x^2=1 := by
  rw [residueElementary_eq_cocode_image] at hx
  obtain ⟨d,hd,rfl⟩ := hx
  have he : d^2=1 := by
    apply Multiplicative.toAdd.injective
    rw [pow_two]
    change d.toAdd+d.toAdd=0
    rw [← two_smul Bit,show (2 : Bit)=0 from rfl,zero_smul]
  rw [← map_pow,he,map_one]

/-- An actual order-three element cannot disappear in the marked elementary quotient. -/
theorem residueQuotient_order_three (S : Finset Omega) (a : residueCentralizer S)
    (ha : orderOf a.val=3) :
    orderOf (QuotientGroup.mk' (residueCentralElementary S) a)=3 := by
  apply orderOf_eq_prime
  · rw [← map_pow]
    have hp : a^3=1 := by
      apply Subtype.ext
      change a.val^3=1
      rw [← ha]
      exact pow_orderOf_eq_one a.val
    rw [hp,map_one]
  · intro h
    have he : a ∈ residueCentralElementary S := (QuotientGroup.eq_one_iff a).mp h
    have hd := orderOf_dvd_of_pow_eq_one (residueElementary_square S a.val he)
    rw [ha] at hd
    norm_num at hd

theorem residueDistinguished_product_order_three (S : Finset Omega) (x y : ResiduePoint S)
    (hxy : orderOf (x.val*y.val)=3) :
    orderOf (residueDistinguishedElement S x * residueDistinguishedElement S y)=3 := by
  change orderOf (QuotientGroup.mk' (residueCentralElementary S) (residuePointCentralizer S x) *
    QuotientGroup.mk' (residueCentralElementary S) (residuePointCentralizer S y))=3
  rw [← map_mul]
  exact residueQuotient_order_three S _ hxy

end Atlas.Fischer
