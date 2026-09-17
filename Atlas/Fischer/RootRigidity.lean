import Atlas.Fischer.CubicSymmetry
import Atlas.Fischer.Roots

namespace Atlas.Fischer

theorem hermitian_sub_left (x y z : Coordinates) :
    hermitian (x - y) z = hermitian x z - hermitian y z := by
  rw [sub_eq_add_neg, hermitian_add_left, ← neg_one_smul Scalar y, hermitian_smul_left]
  simp [sub_eq_add_neg]

theorem hermitian_sub_right (x y z : Coordinates) :
    hermitian x (y - z) = hermitian x y - hermitian x z := by
  rw [sub_eq_add_neg, hermitian_add_right, ← neg_one_smul Scalar z, hermitian_smul_right]
  simp [sub_eq_add_neg]

theorem hermitian_self_eq_zero (x : Coordinates) : hermitian x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    have hp := hermitian_positive x hx
    rw [h, map_zero] at hp
    norm_num at hp
  · rintro rfl
    simp [hermitian, weightedHermitian]

theorem rootMap_add (r x y : Coordinates) : rootMap r (x + y) = rootMap r x + rootMap r y := by
  simp only [rootMap, product_add_left, hermitian_add_right, add_smul]
  abel

/-- The exact antiunitarity hypothesis from the source rigidity lemma. It does not
assert that the root map is multiplicative or involutive. -/
def RootMapAntiunitary (r : Coordinates) : Prop :=
  ∀ x y, hermitian (rootMap r x) (rootMap r y) = star (hermitian x y)

theorem nonorthogonal_root_rigidity (r s : Coordinates) (hr : IsRoot r) (hs : IsRoot s)
    (ha : RootMapAntiunitary r) (hc : hermitian r s ^ 3 = 1) :
    rootMap r s = star (hermitian r s) • s := by
  let c := hermitian r s
  have hunit : star c * c = 1 := cube_root_unit_norm hc
  have hbar : star c ^ 2 = c := by
    rw [cube_root_conjugate hc]
    calc
      (c ^ 2) ^ 2 = c ^ 3 * c := by ring
      _ = c := by rw [hc, one_mul]
  have hsr : hermitian s r = star c := (hermitian_star r s).symm
  have hp : hermitian s (product s r) = 10 * c := by
    change cubic s s r = _
    rw [cubic_swap_last s s r, cubic_swap_first s r s]
    change hermitian r (product s s) = _
    rw [hs.2, hermitian_smul_right]
    simp [c]
  have hst : hermitian s (rootMap r s) = 9 * c := by
    rw [rootMap, hermitian_sub_right, hermitian_smul_right, hp, hsr]
    change 10 * c - star c * star c = 9 * c
    rw [← pow_two, hbar]
    ring
  have hts : hermitian (rootMap r s) s = 9 * star c := by
    rw [← hermitian_star s (rootMap r s), hst]
    simp
  have htt : hermitian (rootMap r s) (rootMap r s) = 9 := by
    rw [ha, hs.1]
    simp
  have hz : hermitian (rootMap r s - star c • s) (rootMap r s - star c • s) = 0 := by
    rw [hermitian_sub_left, hermitian_sub_right, hermitian_sub_right,
      hermitian_smul_right, hermitian_smul_left, hermitian_smul_left,
      hermitian_smul_right, star_star, htt, hts, hst, hs.1]
    calc
      9 - c * (9 * star c) - (star c * (9 * c) - star c * (c * 9)) =
        9 - 9 * (star c * c) := by ring
      _ = 0 := by rw [hunit]; ring
  exact sub_eq_zero.mp ((hermitian_self_eq_zero _).mp hz)

end Atlas.Fischer
