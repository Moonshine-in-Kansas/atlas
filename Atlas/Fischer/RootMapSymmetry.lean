import Atlas.Fischer.RootRigidity

namespace Atlas.Fischer

/-- Cubic symmetry makes the actual conjugate-linear root map symmetric for the
Hermitian form. No root equation is needed for this identity. -/
theorem rootMap_hermitian_symmetric (r x y : Coordinates) :
    hermitian x (rootMap r y) = hermitian y (rootMap r x) := by
  simp only [rootMap, hermitian_sub_right, hermitian_smul_right, hermitian_star]
  change cubic x y r - hermitian y r * hermitian x r =
    cubic y x r - hermitian x r * hermitian y r
  rw [cubic_swap_first x y r, mul_comm (hermitian y r)]

/-- Antiunitarity and cubic symmetry imply involutivity of the actual root map.
This does not assume multiplicativity, root equations, or a choice of matrix gauges. -/
theorem rootMap_involutive_of_antiunitary (r : Coordinates) (ha : RootMapAntiunitary r) :
    Function.Involutive (rootMap r) := by
  intro x
  have hpair (y : Coordinates) :
      hermitian y (rootMap r (rootMap r x)) = hermitian y x := by
    rw [← rootMap_hermitian_symmetric r (rootMap r x) y, ha, hermitian_star]
  apply sub_eq_zero.mp
  apply hermitian_nondegenerate
  intro y
  rw [hermitian_sub_left, ← hermitian_star y (rootMap r (rootMap r x)), hpair,
    hermitian_star, sub_self]

end Atlas.Fischer
