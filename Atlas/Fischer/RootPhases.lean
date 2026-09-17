import Atlas.Fischer.RootRigidity

namespace Atlas.Fischer

theorem root_ne_zero {r : Coordinates} (hr : IsRoot r) : r ≠ 0 := by
  intro h
  have hz := (hermitian_self_eq_zero r).mpr h
  rw [hr.1] at hz
  norm_num at hz

/-- The source's three-element normalized ray is exactly the set of scalar
multiples preserving the root equations, not a full projective line. -/
theorem root_scalar_iff (r : Coordinates) (hr : IsRoot r) (a : Scalar) :
    IsRoot (a • r) ↔ a ^ 3 = 1 := by
  constructor
  · intro hs
    have hn : a * star a = 1 := by
      have h := hs.1
      rw [hermitian_smul_left, hermitian_smul_right, hr.1] at h
      linear_combination h / 9
    have hp : star a ^ 2 = a := by
      have h := hs.2
      rw [product_smul_left, product_smul_right, hr.2,
        smul_smul, smul_smul, smul_smul] at h
      have he := smul_left_injective Scalar (root_ne_zero hr) h
      linear_combination he / 10
    have hc : a ^ 2 = star a := by
      have h := congrArg star hp
      simpa only [star_pow, star_star] using h
    rw [pow_succ, hc, mul_comm, hn]
  · exact root_phase r hr a

theorem negative_not_root {r : Coordinates} (hr : IsRoot r) : ¬IsRoot (-r) := by
  rw [← neg_one_smul Scalar r, root_scalar_iff r hr]
  norm_num

end Atlas.Fischer
