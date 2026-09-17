import Atlas.Fischer.CubicOperatorQuintic

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem rootMap_basis_weighted_symmetry (r : Coordinates) (i a : CoordinateIndex) :
    (coordinateWeight a : Scalar) * rootMap r (coordinateVector i) a =
      (coordinateWeight i : Scalar) * rootMap r (coordinateVector a) i := by
  have h := congrArg star (rootMap_hermitian_symmetric r (coordinateVector a) (coordinateVector i))
  simp only [hermitian_coordinateVector_left, star_mul, star_ratCast, star_star] at h
  simpa only [mul_comm] using h

theorem rootMap_basis_coordinate (r : Coordinates) (i a : CoordinateIndex) :
    rootMap r (coordinateVector i) a = inverseCoordinateMetric a * (coordinateWeight i : Scalar) *
      rootMap r (coordinateVector a) i := by
  have h := congrArg (fun z => inverseCoordinateMetric a * z) (rootMap_basis_weighted_symmetry r i a)
  simpa only [← mul_assoc, inverseCoordinateMetric_mul, one_mul] using h

/-- Weighted row orthogonality of the actual antiunitary root map. -/
theorem rootMap_basis_rows (r : Coordinates) (ha : RootMapAntiunitary r) (a b : CoordinateIndex) :
    (∑ i, inverseCoordinateMetric i * rootMap r (coordinateVector i) a *
      star (rootMap r (coordinateVector i) b)) = if a = b then inverseCoordinateMetric a else 0 := by
  have ht (i : CoordinateIndex) : inverseCoordinateMetric i * rootMap r (coordinateVector i) a *
      star (rootMap r (coordinateVector i) b) = inverseCoordinateMetric a * inverseCoordinateMetric b *
      ((coordinateWeight i : Scalar) * rootMap r (coordinateVector a) i *
        star (rootMap r (coordinateVector b) i)) := by
    rw [rootMap_basis_coordinate r i a, rootMap_basis_coordinate r i b]
    simp only [star_mul, inverseCoordinateMetric_star, star_ratCast]
    calc
      _ = (inverseCoordinateMetric i * (coordinateWeight i : Scalar)) *
        (inverseCoordinateMetric a * inverseCoordinateMetric b *
        ((coordinateWeight i : Scalar) * rootMap r (coordinateVector a) i *
          star (rootMap r (coordinateVector b) i))) := by ring
      _ = _ := by rw [inverseCoordinateMetric_mul, one_mul]
  simp only [ht, ← Finset.mul_sum]
  change inverseCoordinateMetric a * inverseCoordinateMetric b *
    hermitian (rootMap r (coordinateVector a)) (rootMap r (coordinateVector b)) = _
  rw [ha, hermitian_coordinateVector]
  by_cases hab : a = b
  · subst b
    simp only [ite_true, star_ratCast]
    rw [mul_assoc, inverseCoordinateMetric_mul, mul_one]
  · simp [hab]

theorem linearFunctional_coordinate_expansion (f : Coordinates →ₗ[Scalar] Scalar) (x : Coordinates) :
    f x = ∑ a, x a * f (coordinateVector a) := by
  have hx : (∑ a, x a • coordinateVector a) = x := by
    simpa only [Pi.basisFun_apply, Pi.basisFun_repr, coordinateVector] using
      (Pi.basisFun Scalar CoordinateIndex).sum_repr x
  conv_lhs => rw [← hx]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem sum_three_rotate {ι A : Type*} [Fintype ι] [AddCommMonoid A]
    (F : ι → ι → ι → A) : (∑ i, ∑ b, ∑ a, F i b a) = ∑ b, ∑ a, ∑ i, F i b a := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  exact Finset.sum_comm

/-- Every linear functional has unchanged weighted dual norm when evaluated on
the actual antiunitary root-map images of the coordinate basis. -/
theorem linearFunctional_rootMap_norm (r : Coordinates) (ha : RootMapAntiunitary r)
    (f : Coordinates →ₗ[Scalar] Scalar) :
    (∑ i, inverseCoordinateMetric i * f (rootMap r (coordinateVector i)) *
      star (f (rootMap r (coordinateVector i)))) =
      ∑ a, inverseCoordinateMetric a * f (coordinateVector a) * star (f (coordinateVector a)) := by
  have he : (∑ i, inverseCoordinateMetric i * f (rootMap r (coordinateVector i)) *
      star (f (rootMap r (coordinateVector i)))) =
      ∑ b, ∑ a, f (coordinateVector a) * star (f (coordinateVector b)) *
        (∑ i, inverseCoordinateMetric i * rootMap r (coordinateVector i) a *
          star (rootMap r (coordinateVector i) b)) := by
    have hf (i : CoordinateIndex) := linearFunctional_coordinate_expansion f (rootMap r (coordinateVector i))
    conv_lhs => simp only [hf, star_sum, star_mul,
      Finset.mul_sum, Finset.sum_mul]
    rw [sum_three_rotate]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro a haa
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  simp only [rootMap_basis_rows r ha, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro a haa
  ring

end Atlas.Fischer
