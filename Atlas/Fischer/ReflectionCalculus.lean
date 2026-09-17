import Atlas.Fischer.ReflectingRootAutomorphisms
import Atlas.Fischer.ReflectingRootRays
import Atlas.Fischer.RootTensorTheorem

noncomputable section
namespace Atlas.Fischer

/-- Intrinsic reflecting roots define actual algebra involutions. -/
def reflectingRootAutomorphism (r : Coordinates) (hr : IsReflectingRoot r) :
    SemilinearAlgebraAutomorphism := rootAlgebraAutomorphism r hr.1.1 hr.1.2 hr.2.1

@[simp] theorem reflectingRootAutomorphism_apply (r : Coordinates) (hr : IsReflectingRoot r)
    (x : Coordinates) : (reflectingRootAutomorphism r hr).val x = rootMap r x := rfl

theorem reflectingRoot_rootMap_self (r : Coordinates) (hr : IsReflectingRoot r) : rootMap r r = r := by
  rw [rootMap,hr.1.1,hr.1.2]
  module

/-- Actual conjugation of root maps, before passing to ray permutations. -/
theorem reflectingRoot_conjugation (r s : Coordinates) (hr : IsReflectingRoot r)
    (x : Coordinates) : rootMap (rootMap r s) x = rootMap r (rootMap s (rootMap r x)) := by
  have he := semilinearAlgebra_rootMap (reflectingRootAutomorphism r hr) s (rootMap r x)
  simp only [reflectingRootAutomorphism_apply,hr.2.2.1 x] at he
  exact he

theorem reflectingRoot_image (r s : Coordinates) (hr : IsReflectingRoot r)
    (hs : IsReflectingRoot s) : IsReflectingRoot (rootMap r s) :=
  semilinearAlgebra_isReflectingRoot (reflectingRootAutomorphism r hr) s hs

theorem rootMap_zero_pairing (r s : Coordinates) (h : hermitian r s=0) :
    rootMap r s=product r s := by
  rw [rootMap,h,zero_smul,sub_zero,product_comm]

/-- Zero-pairing roots satisfy the literal braid relation in the algebra. -/
theorem reflectingRoot_braid (r s : Coordinates) (hr : IsReflectingRoot r)
    (hs : IsReflectingRoot s) (h : hermitian r s=0) (x : Coordinates) :
    rootMap r (rootMap s (rootMap r x)) = rootMap s (rootMap r (rootMap s x)) := by
  have hs0 : hermitian s r=0 := by rw [← hermitian_star r s,h,star_zero]
  rw [← reflectingRoot_conjugation r s hr,← reflectingRoot_conjugation s r hs,
    rootMap_zero_pairing r s h,rootMap_zero_pairing s r hs0,product_comm r s]

/-- The braid relation gives the cube identity; exact order is a separate
ray-permutation assertion requiring distinctness. -/
theorem reflectingRoot_product_cube (r s : Coordinates) (hr : IsReflectingRoot r)
    (hs : IsReflectingRoot s) (h : hermitian r s=0) (x : Coordinates) :
    rootMap r (rootMap s (rootMap r (rootMap s (rootMap r (rootMap s x))))) = x := by
  rw [reflectingRoot_braid r s hr hs h,hs.2.2.1,hr.2.2.1,hs.2.2.1]

/-- Nonzero cubic-unit pairing determines the actual product, with the
conjugate on the second coefficient in the source convention. -/
theorem reflectingRoot_unit_product (r s : Coordinates) (hr : IsReflectingRoot r)
    (hs : IsReflectingRoot s) (h : hermitian r s ^ 3=1) :
    product r s = hermitian r s • r + star (hermitian r s) • s := by
  have he := nonorthogonal_root_rigidity r s hr.1 hs.1 hr.2.1 h
  rw [rootMap,product_comm s r] at he
  rw [sub_eq_iff_eq_add] at he
  exact he.trans (add_comm _ _)

/-- The square is the actual cubic scalar; scalars are only killed after
passing to normalized ray permutations. -/
theorem reflectingRoot_unit_product_square (r s : Coordinates) (hr : IsReflectingRoot r)
    (hs : IsReflectingRoot s) (h : hermitian r s ^ 3=1) (x : Coordinates) :
    rootMap r (rootMap s (rootMap r (rootMap s x))) = hermitian r s • x := by
  have hc : (star (hermitian r s))^3=1 := by rw [← star_pow,h,star_one]
  have hc2 : (star (hermitian r s))^2=hermitian r s := by
    simpa only [star_star] using (cube_root_conjugate hc).symm
  rw [← reflectingRoot_conjugation r s hr,
    nonorthogonal_root_rigidity r s hr.1 hs.1 hr.2.1 h,
    rootMap_phase s _ _ hc,hc2,hs.2.2.1]

/-- Root-scalar independence holds for the induced normalized ray image. -/
theorem rootMap_phase_ray (r x : Coordinates) (a : Scalar) (ha : a^3=1) :
    rootRay (rootMap (a • r) x)=rootRay (rootMap r x) := by
  rw [rootMap_phase r x a ha]
  apply rootRay_phase
  rw [← pow_mul,Nat.mul_comm 2 3,pow_mul,ha]
  simp

/-- Conjugate-linearity likewise makes the input ray representative irrelevant. -/
theorem rootMap_input_phase_ray (r x : Coordinates) (a : Scalar) (ha : a^3=1) :
    rootRay (rootMap r (a • x))=rootRay (rootMap r x) := by
  rw [rootMap_smul]
  apply rootRay_phase
  rw [← star_pow,ha,star_one]

end Atlas.Fischer
