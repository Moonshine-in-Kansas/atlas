import Atlas.Fischer.RootMapEquivalence
import Atlas.Fischer.WeightedCubicTensor

noncomputable section
namespace Atlas.Fischer

/-- Conjugating the cubic after the conjugate-linear root map makes it trilinear. -/
def rootTwistedCubic (r x y z : Coordinates) : Scalar :=
  star (cubic (rootMap r x) (rootMap r y) (rootMap r z))

def rootTwistedCubicTrilinear (r : Coordinates) :
    Coordinates →ₗ[Scalar] Coordinates →ₗ[Scalar] Coordinates →ₗ[Scalar] Scalar where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => rootTwistedCubic r x y z
          map_add' := by
            intro z w
            simp only [rootTwistedCubic, rootMap_add, cubic_add_third, star_add]
          map_smul' := by
            intro a z
            simp only [rootTwistedCubic, rootMap_smul, cubic_smul_third,
              star_mul, star_star, RingHom.id_apply, smul_eq_mul]
            ring }
      map_add' := by
        intro y w
        apply LinearMap.ext
        intro z
        change rootTwistedCubic r x (y + w) z = _
        simp only [rootTwistedCubic, rootMap_add, cubic_add_second, star_add]
        rfl
      map_smul' := by
        intro a y
        apply LinearMap.ext
        intro z
        change rootTwistedCubic r x (a • y) z = a * rootTwistedCubic r x y z
        simp only [rootTwistedCubic, rootMap_smul, cubic_smul_second, star_mul, star_star]
        ring }
  map_add' := by
    intro x w
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    change rootTwistedCubic r (x + w) y z = _
    simp only [rootTwistedCubic, rootMap_add, cubic_add_first, star_add]
    rfl
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    change rootTwistedCubic r (a • x) y z = a * rootTwistedCubic r x y z
    simp only [rootTwistedCubic, rootMap_smul, cubic_smul_first, star_mul, star_star]
    ring

theorem rootTwistedCubic_eq_of_basis (r : Coordinates)
    (h : ∀ i j k : CoordinateIndex,
      rootTwistedCubic r (coordinateVector i) (coordinateVector j) (coordinateVector k) =
        coordinateCubic i j k) (x y z : Coordinates) :
    rootTwistedCubic r x y z = cubic x y z := by
  have he : rootTwistedCubicTrilinear r = cubicTrilinear := by
    apply (Pi.basisFun Scalar CoordinateIndex).ext
    intro i
    apply (Pi.basisFun Scalar CoordinateIndex).ext
    intro j
    apply (Pi.basisFun Scalar CoordinateIndex).ext
    intro k
    change rootTwistedCubic r ((Pi.basisFun Scalar CoordinateIndex) i)
      ((Pi.basisFun Scalar CoordinateIndex) j) ((Pi.basisFun Scalar CoordinateIndex) k) =
        cubic ((Pi.basisFun Scalar CoordinateIndex) i)
          ((Pi.basisFun Scalar CoordinateIndex) j) ((Pi.basisFun Scalar CoordinateIndex) k)
    simpa only [Pi.basisFun_apply, coordinateVector, coordinateCubic] using h i j k
  exact congrArg (fun f : Coordinates →ₗ[Scalar] Coordinates →ₗ[Scalar]
    Coordinates →ₗ[Scalar] Scalar => f x y z) he

theorem rootMap_product_of_cubic (r : Coordinates) (ha : RootMapAntiunitary r)
    (hc : ∀ x y z, cubic (rootMap r x) (rootMap r y) (rootMap r z) = star (cubic x y z))
    (x y : Coordinates) : rootMap r (product x y) = product (rootMap r x) (rootMap r y) := by
  apply sub_eq_zero.mp
  apply hermitian_nondegenerate
  intro w
  obtain ⟨z, rfl⟩ := (rootMap_involutive_of_antiunitary r ha).surjective w
  have hp : hermitian (product (rootMap r x) (rootMap r y)) (rootMap r z) = cubic z x y := by
    rw [← hermitian_star]
    change star (cubic (rootMap r z) (rootMap r x) (rootMap r y)) = _
    rw [hc, star_star]
  rw [hermitian_sub_left, ha, hermitian_star, hp]
  exact sub_self _

abbrev CubicTensorIndex := CoordinateIndex × CoordinateIndex × CoordinateIndex

def cubicTensorWeight (t : CubicTensorIndex) : ℚ :=
  (coordinateWeight t.1 * coordinateWeight t.2.1 * coordinateWeight t.2.2)⁻¹

theorem cubicTensorWeight_positive (t : CubicTensorIndex) : 0 < cubicTensorWeight t :=
  inv_pos.mpr (mul_pos (mul_pos (coordinateWeight_positive _) (coordinateWeight_positive _))
    (coordinateWeight_positive _))

def rootCubicDefect (r : Coordinates) (t : CubicTensorIndex) : Scalar :=
  rootTwistedCubic r (coordinateVector t.1) (coordinateVector t.2.1)
    (coordinateVector t.2.2) - coordinateCubic t.1 t.2.1 t.2.2

def rootCubicDefectNorm (r : Coordinates) : Scalar :=
  weightedHermitian cubicTensorWeight (rootCubicDefect r) (rootCubicDefect r)

/-- Positive definiteness turns an exact zero defect norm into actual multiplicativity.
The zero-norm hypothesis is retained until the numerical tensor argument proves it. -/
theorem rootMap_product_of_defectNorm_zero (r : Coordinates) (ha : RootMapAntiunitary r)
    (hn : rootCubicDefectNorm r = 0) (x y : Coordinates) :
    rootMap r (product x y) = product (rootMap r x) (rootMap r y) := by
  have hz : rootCubicDefect r = 0 := by
    by_contra h
    have hp := weightedHermitian_positive cubicTensorWeight cubicTensorWeight_positive
      (rootCubicDefect r) h
    change Atlas.Algebra.eisensteinReal (rootCubicDefectNorm r) > 0 at hp
    rw [hn] at hp
    norm_num [Atlas.Algebra.eisensteinReal] at hp
  apply rootMap_product_of_cubic r ha ?_ x y
  intro a b c
  have he := rootTwistedCubic_eq_of_basis r (fun i j k => by
    have ht := congrFun hz (i, j, k)
    change rootTwistedCubic r (coordinateVector i) (coordinateVector j) (coordinateVector k) -
      coordinateCubic i j k = 0 at ht
    exact sub_eq_zero.mp ht) a b c
  simpa only [rootTwistedCubic, star_star] using congrArg star he

end Atlas.Fischer
