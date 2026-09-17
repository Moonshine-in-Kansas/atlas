import Atlas.Fischer.CubicForm
import Atlas.Fischer.OctadCubicCoefficients
import Atlas.Fischer.AxisProductCoefficients

namespace Atlas.Fischer
open Atlas.Codes

private theorem mixed_cubic_coefficient (i : Omega) (O P : Octad) :
    (1 / 8 : Scalar) * star (octadBasisProduct O P (Sum.inl i)) =
      star (axisOctadBasisProduct i P (Sum.inr O)) := by
  classical
  rw [octadBasisProduct_axis_apply, axisOctadBasisProduct_octad_apply]
  by_cases h : O = P
  · subst P
    by_cases hi : i ∈ O.val <;> norm_num [hi]
  · simp [h]

/-- All support types are covered symbolically. The WWW case uses the actual
Parker triangle and complementary-trio identities. -/
theorem cubic_basis_swap_first (a b c : CoordinateIndex) :
    cubic (coordinateVector a) (coordinateVector b) (coordinateVector c) =
      cubic (coordinateVector b) (coordinateVector a) (coordinateVector c) := by
  classical
  simp only [cubic, product_coordinateVector, hermitian_coordinateVector_left]
  cases a with
  | inl i => cases b with
    | inl j => cases c with
      | inl k => simp only [basisProduct, coordinateWeight]; rw [axisBasisProduct_cubic_switch]
      | inr O => simp [basisProduct, coordinateWeight]
    | inr O => cases c with
      | inl j => simp [basisProduct, coordinateWeight]
      | inr P => simpa only [basisProduct, coordinateWeight, Rat.cast_one,
          Rat.cast_div, Rat.cast_ofNat, one_mul] using mixed_cubic_coefficient i O P
  | inr O => cases b with
    | inl i => cases c with
      | inl j => simp [basisProduct, coordinateWeight]
      | inr P => simpa only [basisProduct, coordinateWeight, Rat.cast_one,
          Rat.cast_div, Rat.cast_ofNat, one_mul] using (mixed_cubic_coefficient i O P).symm
    | inr P => cases c with
      | inl i =>
        simp only [basisProduct, coordinateWeight, Rat.cast_one, one_mul,
          axisOctadBasisProduct_octad_apply]
        by_cases h : O = P
        · subst P; rfl
        · simp [h, Ne.symm h]
      | inr Q => simp only [basisProduct, coordinateWeight, Rat.cast_one, one_mul]
                 rw [octadBasisProduct_cubic_switch]

/-- The actual exact cubic tensor, bundled as a trilinear map over E. -/
noncomputable def cubicTrilinear :
    Coordinates →ₗ[Scalar] Coordinates →ₗ[Scalar] Coordinates →ₗ[Scalar] Scalar where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => cubic x y z
          map_add' := cubic_add_third x y
          map_smul' := fun a z => cubic_smul_third a x y z }
      map_add' := fun y y' => by apply LinearMap.ext; intro z; exact cubic_add_second x y y' z
      map_smul' := fun a y => by apply LinearMap.ext; intro z; exact cubic_smul_second a x y z }
  map_add' x x' := by apply LinearMap.ext; intro y; apply LinearMap.ext; intro z; exact cubic_add_first x x' y z
  map_smul' a x := by apply LinearMap.ext; intro y; apply LinearMap.ext; intro z; exact cubic_smul_first a x y z

theorem cubic_swap_first (x y z : Coordinates) : cubic x y z = cubic y x z := by
  classical
  have he : cubicTrilinear = cubicTrilinear.flip := by
    apply (Pi.basisFun Scalar CoordinateIndex).ext
    intro i
    apply (Pi.basisFun Scalar CoordinateIndex).ext
    intro j
    apply (Pi.basisFun Scalar CoordinateIndex).ext
    intro k
    change cubic ((Pi.basisFun Scalar CoordinateIndex) i)
      ((Pi.basisFun Scalar CoordinateIndex) j) ((Pi.basisFun Scalar CoordinateIndex) k) =
      cubic ((Pi.basisFun Scalar CoordinateIndex) j)
        ((Pi.basisFun Scalar CoordinateIndex) i) ((Pi.basisFun Scalar CoordinateIndex) k)
    simpa only [Pi.basisFun_apply, coordinateVector] using cubic_basis_swap_first i j k
  exact congrArg (fun f : Coordinates →ₗ[Scalar] Coordinates →ₗ[Scalar]
    Coordinates →ₗ[Scalar] Scalar => f x y z) he

end Atlas.Fischer
