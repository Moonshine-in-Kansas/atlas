import Atlas.Fischer.GeneratedRayParity
import Atlas.Algebra.PGroupPrimeOrder

noncomputable section
namespace Atlas.Fischer

/-- Orthogonal displayed roots give exact order three in the actual group. -/
theorem distinguishedRootElement_zero_order (i j : ReflectingRootParameter)
    (h : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)=0) :
    orderOf (distinguishedRootElement i * distinguishedRootElement j)=3 := by
  have hij : i ≠ j := by
    intro he
    subst j
    rw [(reflectingRootParameter_isReflectingRoot i).1.1] at h
    norm_num at h
  rw [distinguishedRootElement_product_order i j hij,if_pos h]

theorem distinguishedRootElement_nonzero_square (i j : ReflectingRootParameter)
    (h : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j) ≠ 0) :
    (distinguishedRootElement i * distinguishedRootElement j)^2=1 := by
  by_cases hij : i=j
  · subst j
    rw [distinguishedRootElement_mul_self,one_pow]
  · have ho := distinguishedRootElement_product_order i j hij
    rw [if_neg h] at ho
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [ho])

/-- Modulo a p-group with p different from three, the quotient still detects
the commuting/noncommuting distinction on all displayed pairs, including equality. -/
theorem distinguishedRootElement_quotient_square_iff {H : Type*} [Group H]
    {p : ℕ} [Fact p.Prime] (f : rootGeneratedRayGroup →* H)
    (hk : IsPGroup p f.ker) (hp : p ≠ 3) (i j : ReflectingRootParameter) :
    (f (distinguishedRootElement i * distinguishedRootElement j))^2=1 ↔
      hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j) ≠ 0 := by
  constructor
  · intro hs hz
    have ho := Atlas.Algebra.orderOf_map_prime_of_pgroup_kernel f hk (by decide : Nat.Prime 3)
      hp _ (distinguishedRootElement_zero_order i j hz)
    have hd := orderOf_dvd_of_pow_eq_one hs
    rw [ho] at hd
    norm_num at hd
  · intro h
    rw [← map_pow,distinguishedRootElement_nonzero_square i j h,map_one]

/-- Distinct basic pair products retain exact order two modulo an odd p-group. -/
theorem basic_pair_quotient_order {H : Type*} [Group H] {p : ℕ} [Fact p.Prime]
    (f : rootGeneratedRayGroup →* H) (hk : IsPGroup p f.ker) (hp : p ≠ 2)
    (i j : Atlas.Codes.Omega) (hij : i ≠ j) :
    orderOf (f (distinguishedRootElement (.inl i) * distinguishedRootElement (.inl j)))=2 := by
  apply Atlas.Algebra.orderOf_map_prime_of_pgroup_kernel f hk (by decide : Nat.Prime 2) hp
  rw [distinguishedRootElement_product_order _ _ (by simpa using hij)]
  change (if hermitian (basicAxis i) (basicAxis j)=0 then 3 else 2)=2
  rw [hermitian_basicAxis_basicAxis,if_neg hij]
  norm_num

end Atlas.Fischer
