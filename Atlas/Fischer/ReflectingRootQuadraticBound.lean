import Atlas.Fischer.ReflectingRootQuadraticMetric
import Atlas.Fischer.ReflectingRootPairing

noncomputable section
namespace Atlas.Fischer

/-- Every finite family of intrinsic reflecting roots on distinct Mu3 rays obeys
 the absolute bound. No finiteness or exhaustion of all reflecting roots is assumed. -/
theorem reflectingRoot_complex_squares_independent {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j = (a.val.val : Scalar) • r i) :
    LinearIndependent ℂ (fun j => Atlas.Algebra.euclideanSymmetricSquare
      (reflectingRootEuclidean (r j))) := by
  exact Atlas.Algebra.symmetricMatrixSquare_linearIndependent (fun j => reflectingRootEuclidean (r j))
    9 (by norm_num)
    (fun j => by rw [reflectingRootEuclidean_inner, (hr j).1.1]; simp only [map_ofNat]; norm_num)
    (fun i j hij => by
      rw [reflectingRootEuclidean_inner]
      have hd' : ¬ ∃ a : Scalar, a ^ 3 = 1 ∧ r i = a • r j := by
        rintro ⟨a, ha, he⟩
        exact hd j i hij.symm ⟨rootsOfUnity.mkOfPowEq a ha, he⟩
      have hh := congrArg scalarToComplex
        (reflectingRoot_pairing_square (r j) (r i) (hr j) (hr i) hd')
      simpa only [map_pow, scalarToComplex_star] using hh)

/-- Absolute bound for an arbitrary finite family of intrinsic reflecting rays. -/
theorem reflectingRoot_finite_family_bound {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j = (a.val.val : Scalar) • r i) :
    Fintype.card J ≤ 306936 := by
  have h := (reflectingRoot_complex_squares_independent r hr hd).fintype_card_le_finrank
  rw [Atlas.Algebra.symmetricMatrixSpace_finrank, coordinateIndex_card] at h
  norm_num [Nat.choose_two_right] at h ⊢
  exact h

end Atlas.Fischer

