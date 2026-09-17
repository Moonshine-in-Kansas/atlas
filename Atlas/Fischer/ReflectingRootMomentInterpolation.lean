import Atlas.Fischer.ReflectingRootMomentOperators

noncomputable section
namespace Atlas.Fischer

/-- Compose the actual product with an E-linear output map. -/
def linearAfterCoordinateProduct (T : Module.End Scalar Coordinates) :
    Coordinates →ₛₗ[starRingEnd Scalar] Coordinates →ₛₗ[starRingEnd Scalar] Coordinates where
  toFun x :=
    { toFun := fun y => T (product x y)
      map_add' := by intro y z; rw [product_add_right,map_add]
      map_smul' := by intro a y; rw [product_smul_right,map_smul]; rfl }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    simp only [LinearMap.add_apply,product_add_left,map_add]
    rfl
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    simp only [LinearMap.smul_apply,product_smul_left,map_smul]
    rfl

/-- Quadratic interpolation from the full reflecting-square basis. The actual
family cardinality and distinctness are explicit hypotheses. -/
theorem reflectingMomentProduct_interpolation_ten {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) (x y : Coordinates) :
    (10 : Scalar) • reflectingMomentProduct r x y=
      reflectingFrameOperator r (product x y)+(72 : Scalar) • product x y := by
  let T : Module.End Scalar Coordinates := reflectingFrameOperator r+(72 : Scalar) • 1
  have h := Atlas.Algebra.symmetricMatrixProduct_ext (starRingEnd Scalar)
    (reflectingRootSquareBasis r hr hd hc) r (reflectingRootSquareBasis_apply r hr hd hc)
    (by norm_num) ((10 : Scalar) • reflectingMomentProduct r) (linearAfterCoordinateProduct T)
    (by intro u v; simp only [LinearMap.smul_apply,reflectingMomentProduct_comm r u v])
    (by intro u v; change T (product u v)=T (product v u); rw [product_comm])
    (by
      intro j
      change (10 : Scalar) • reflectingMomentProduct r (r j) (r j)=T (product (r j) (r j))
      rw [reflectingMomentProduct_diagonal r hr hd j,(hr j).1.2,map_smul]
      rfl)
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

theorem reflectingMomentProduct_interpolation {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) (x y : Coordinates) :
    reflectingMomentProduct r x y=(1 / 10 : Scalar) •
      (reflectingFrameOperator r (product x y)+(72 : Scalar) • product x y) := by
  linear_combination (norm := module) (1 / 10 : Scalar) •
    reflectingMomentProduct_interpolation_ten r hr hd hc x y

/-- Symmetry of the cubic moment transfers to the interpolated frame operator. -/
theorem reflectingFrameOperator_cubic_swap {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) (x y z : Coordinates) :
    hermitian x (reflectingFrameOperator r (product y z))=
      hermitian y (reflectingFrameOperator r (product x z)) := by
  have h1 := congrArg (hermitian x) (reflectingMomentProduct_interpolation_ten r hr hd hc y z)
  have h2 := congrArg (hermitian y) (reflectingMomentProduct_interpolation_ten r hr hd hc x z)
  have hb := reflectingMomentProduct_cubic_swap r x y z
  have hC : hermitian x (product y z)=hermitian y (product x z) := cubic_swap_first x y z
  simp only [hermitian_smul_right,hermitian_add_right] at h1 h2
  norm_num at h1 h2
  rw [hb,hC] at h1
  linear_combination h2-h1

/-- The actual finite frame operator belongs to the centroid, derived from
self-adjointness and the symmetric cubic moment rather than irreducibility. -/
theorem reflectingFrameOperator_centroid {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) : IsProductCentroid (reflectingFrameOperator r) := by
  have he (x y : Coordinates) : reflectingFrameOperator r (product x y)=
      product (reflectingFrameOperator r x) y := by
    apply sub_eq_zero.mp
    apply hermitian_nondegenerate
    intro z
    rw [hermitian_sub_left]
    apply sub_eq_zero.mpr
    apply star_injective
    rw [hermitian_star,hermitian_star]
    calc
      _ = hermitian x (reflectingFrameOperator r (product z y)) :=
        reflectingFrameOperator_cubic_swap r hr hd hc z x y
      _ = hermitian (reflectingFrameOperator r x) (product z y) :=
        (reflectingFrameOperator_selfadjoint r x (product z y)).symm
      _ = _ := cubic_swap_first (reflectingFrameOperator r x) z y
  intro x y
  exact ⟨he x y,by rw [product_comm x y,he y x,product_comm]⟩

end Atlas.Fischer
