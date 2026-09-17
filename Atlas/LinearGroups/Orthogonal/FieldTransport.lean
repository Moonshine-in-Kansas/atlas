import Atlas.LinearGroups.Orthogonal.SemilinearTransport

/-! # Coordinatewise field transport of the actual B and split D quadratic models -/
noncomputable section
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
namespace Atlas.Orthogonal
variable {n : ℕ} {F K : Type*} [Field F] [Field K]

def fieldCoordinatesD (e : F ≃+* K) : VectorD n F ≃ₛₗ[RingHomClass.toRingHom e] VectorD n K where
  toFun x i := e (x i)
  invFun x i := e.symm (x i)
  left_inv x := by funext i; exact e.symm_apply_apply (x i)
  right_inv x := by funext i; exact e.apply_symm_apply (x i)
  map_add' x y := by funext i; exact map_add e (x i) (y i)
  map_smul' a x := by funext i; exact map_mul e a (x i)

def fieldCoordinatesB (e : F ≃+* K) : VectorB n F ≃ₛₗ[RingHomClass.toRingHom e] VectorB n K where
  toFun x := (fieldCoordinatesD e x.1, e x.2)
  invFun x := ((fieldCoordinatesD e).symm x.1, e.symm x.2)
  left_inv x := Prod.ext ((fieldCoordinatesD e).symm_apply_apply x.1) (e.symm_apply_apply x.2)
  right_inv x := Prod.ext ((fieldCoordinatesD e).apply_symm_apply x.1) (e.apply_symm_apply x.2)
  map_add' x y := Prod.ext (map_add (fieldCoordinatesD e) x.1 y.1) (map_add e x.2 y.2)
  map_smul' a x := Prod.ext (map_smulₛₗ (fieldCoordinatesD e) a x.1) (map_mul e a x.2)

theorem fieldCoordinatesD_form (e : F ≃+* K) (x : VectorD n F) :
    formD n K (fieldCoordinatesD e x) = e (formD n F x) := by
  rw [formD_apply, formD_apply]
  change (∑ i : Fin n, e (x (.inl i)) * e (x (.inr i))) =
    e (∑ i : Fin n, x (.inl i) * x (.inr i))
  simp only [map_sum, map_mul]

theorem fieldCoordinatesB_form (e : F ≃+* K) (x : VectorB n F) :
    formB n K (fieldCoordinatesB e x) = e (formB n F x) := by
  rw [formB_apply, formB_apply]
  change formD n K (fieldCoordinatesD e x.1) + (e x.2)^2 =
    e (formD n F x.1 + x.2^2)
  rw [fieldCoordinatesD_form, map_add, map_pow]

/-- Field transport of the full split-D quadratic isometry group. -/
def fieldEquivFullD (e : F ≃+* K) : O_DPlus n F ≃* O_DPlus n K :=
  semilinearIsometryGroupTransport e (fieldCoordinatesD e) (formD n F) (formD n K)
    (fieldCoordinatesD_form e)

/-- Field transport of the full B quadratic isometry group. -/
def fieldEquivFullB (e : F ≃+* K) : O_B n F ≃* O_B n K :=
  semilinearIsometryGroupTransport e (fieldCoordinatesB e) (formB n F) (formB n K)
    (fieldCoordinatesB_form e)

end Atlas.Orthogonal
