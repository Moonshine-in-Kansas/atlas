import Atlas.Fischer.RootMapDualNorm

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators

/-- Weighted squared norm of the actual cubic evaluated on three coordinate-map families. -/
def cubicImageNorm (f g h : Coordinates → Coordinates) : Scalar :=
  ∑ i, inverseCoordinateMetric i * ∑ j, inverseCoordinateMetric j *
    ∑ k, inverseCoordinateMetric k * cubic (f (coordinateVector i)) (g (coordinateVector j)) (h (coordinateVector k)) *
      star (cubic (f (coordinateVector i)) (g (coordinateVector j)) (h (coordinateVector k)))

theorem cubicImageNorm_swap_first (f g h : Coordinates → Coordinates) :
    cubicImageNorm f g h = cubicImageNorm g f h := by
  simp only [cubicImageNorm, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [cubic_swap_first (f (coordinateVector j)) (g (coordinateVector i)) (h (coordinateVector k))]
  ring

theorem cubicImageNorm_swap_last (f g h : Coordinates → Coordinates) :
    cubicImageNorm f g h = cubicImageNorm f h g := by
  simp only [cubicImageNorm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [cubic_swap_last (f (coordinateVector i)) (g (coordinateVector k)) (h (coordinateVector j))]
  ring

theorem cubicImageNorm_rootMap_last (r : Coordinates) (ha : RootMapAntiunitary r)
    (f g : Coordinates → Coordinates) : cubicImageNorm f g (rootMap r) = cubicImageNorm f g id := by
  unfold cubicImageNorm
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact linearFunctional_rootMap_norm r ha (cubicTrilinear (f (coordinateVector i)) (g (coordinateVector j)))

/-- Antiunitarity preserves cubic tensor norm, without preserving multiplication. -/
theorem cubicImageNorm_rootMap (r : Coordinates) (ha : RootMapAntiunitary r) :
    cubicImageNorm (rootMap r) (rootMap r) (rootMap r) = cubicImageNorm id id id := by
  rw [cubicImageNorm_rootMap_last r ha,
    cubicImageNorm_swap_last (rootMap r) (rootMap r) id,
    cubicImageNorm_rootMap_last r ha,
    cubicImageNorm_swap_first (rootMap r) id id,
    cubicImageNorm_swap_last id (rootMap r) id,
    cubicImageNorm_rootMap_last r ha]

theorem cubicImageNorm_id : cubicImageNorm id id id = coordinateCubicNorm := by
  simp only [cubicImageNorm, coordinateCubicNorm, coordinateCubicSlice,
    coordinateCubic, id_eq, Finset.mul_sum, mul_assoc]

end Atlas.Fischer
