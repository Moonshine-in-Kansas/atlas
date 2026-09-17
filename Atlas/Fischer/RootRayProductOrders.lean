import Atlas.Fischer.RootRayCovariance
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
namespace Atlas.Fischer

theorem displayedRootRayInvolution_self (i : ReflectingRootParameter) :
    displayedRootRayInvolution i (displayedRayOfParameter i)=displayedRayOfParameter i := by
  apply Subtype.ext
  rw [displayedRootRayInvolution_parameter_value,
    reflectingRoot_rootMap_self _ (reflectingRootParameter_isReflectingRoot i)]
  rfl

theorem displayedRootRayInvolution_fixed_iff (i j : ReflectingRootParameter) :
    displayedRootRayInvolution i (displayedRayOfParameter j)=displayedRayOfParameter j ↔
      hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j) ≠ 0 := by
  rw [Subtype.ext_iff,displayedRootRayInvolution_parameter_value]
  exact reflectingRoot_fixed_ray_iff _ _ (reflectingRootParameter_isReflectingRoot i)
    (reflectingRootParameter_isReflectingRoot j)

theorem displayedRootRay_zero_product_ne_one (i j : ReflectingRootParameter)
    (h : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)=0) :
    displayedRootRayInvolution i * displayedRootRayInvolution j ≠ 1 := by
  intro he
  have hf := congrArg (fun e : Equiv.Perm DisplayedReflectingRay => e (displayedRayOfParameter j)) he
  change displayedRootRayInvolution i (displayedRootRayInvolution j (displayedRayOfParameter j)) =
    displayedRayOfParameter j at hf
  rw [displayedRootRayInvolution_self] at hf
  exact ((displayedRootRayInvolution_fixed_iff i j).mp hf) h

theorem reflectingRootAutomorphism_product_cube (r s : Coordinates)
    (hr : IsReflectingRoot r) (hs : IsReflectingRoot s) (h : hermitian r s=0) :
    (reflectingRootAutomorphism r hr * reflectingRootAutomorphism s hs)^3=1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change rootMap r (rootMap s (rootMap r (rootMap s (rootMap r (rootMap s x)))))=x
  exact reflectingRoot_product_cube r s hr hs h x

/-- Exact order three on a zero edge follows from the cube identity and an
actual moved ray, rather than from a power relation alone. -/
theorem displayedRootRay_zero_product_order (i j : ReflectingRootParameter)
    (h : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)=0) :
    orderOf (displayedRootRayInvolution i * displayedRootRayInvolution j)=3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime
  · rw [displayedRootRayInvolution,displayedRootRayInvolution,← map_mul,← map_pow]
    rw [show (displayedRootAutomorphism i * displayedRootAutomorphism j)^3=1 from
      reflectingRootAutomorphism_product_cube _ _ (reflectingRootParameter_isReflectingRoot i)
        (reflectingRootParameter_isReflectingRoot j) h,map_one]
  · exact displayedRootRay_zero_product_ne_one i j h

/-- Unit-pairing scalar squares act trivially on normalized rays. -/
theorem displayedRootRay_unit_product_square (i j : ReflectingRootParameter)
    (h : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)^3=1) :
    (displayedRootRayInvolution i * displayedRootRayInvolution j)^2=1 := by
  rw [displayedRootRayInvolution,displayedRootRayInvolution,← map_mul,← map_pow]
  apply Equiv.ext
  intro R
  obtain ⟨t,rfl⟩ := displayedRayOfParameter_surjective R
  apply Subtype.ext
  rw [semilinearDisplayedRayAction_parameter_value]
  change rootRay (rootMap (reflectingRootParameterVector i)
    (rootMap (reflectingRootParameterVector j) (rootMap (reflectingRootParameterVector i)
      (rootMap (reflectingRootParameterVector j) (reflectingRootParameterVector t))))) = _
  rw [reflectingRoot_unit_product_square _ _ (reflectingRootParameter_isReflectingRoot i)
    (reflectingRootParameter_isReflectingRoot j) h,rootRay_phase _ _ h]
  rfl

/-- Every displayed generator moves a ray: the verified zero valency is positive. -/
theorem displayedRootRayInvolution_ne_one (i : ReflectingRootParameter) :
    displayedRootRayInvolution i ≠ 1 := by
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 <
    (reflectingZeroNeighbors reflectingRootParameterVector i).card by
      rw [reflectingFamily_zero_valency]; norm_num)
  have hz : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)=0 := by
    simpa [reflectingZeroNeighbors] using hj
  intro he
  have hf : displayedRootRayInvolution i (displayedRayOfParameter j)=displayedRayOfParameter j := by rw [he]; rfl
  exact ((displayedRootRayInvolution_fixed_iff i j).mp hf) hz

theorem displayedRootRayInvolution_order (i : ReflectingRootParameter) :
    orderOf (displayedRootRayInvolution i)=2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact orderOf_eq_prime (displayedRootRayInvolution_square i) (displayedRootRayInvolution_ne_one i)

theorem displayedRootRayInvolution_inv (i : ReflectingRootParameter) :
    (displayedRootRayInvolution i)⁻¹=displayedRootRayInvolution i :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using displayedRootRayInvolution_square i)

/-- Unit pairing gives commuting actual ray involutions. -/
theorem displayedRootRay_unit_commute (i j : ReflectingRootParameter)
    (h : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)^3=1) :
    Commute (displayedRootRayInvolution i) (displayedRootRayInvolution j) := by
  have he := inv_eq_of_mul_eq_one_right
    (show (displayedRootRayInvolution i * displayedRootRayInvolution j) *
      (displayedRootRayInvolution i * displayedRootRayInvolution j)=1 by
        simpa only [pow_two] using displayedRootRay_unit_product_square i j h)
  change displayedRootRayInvolution i * displayedRootRayInvolution j =
    displayedRootRayInvolution j * displayedRootRayInvolution i
  rw [← he,mul_inv_rev,displayedRootRayInvolution_inv,displayedRootRayInvolution_inv]

end Atlas.Fischer

