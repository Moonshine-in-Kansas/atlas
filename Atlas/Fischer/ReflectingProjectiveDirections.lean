import Atlas.Fischer.TripleCover
import Mathlib.LinearAlgebra.Projectivization.Basic

noncomputable section
namespace Atlas.Fischer

/-- For normalized roots, equality of genuine projective directions is exactly
 equality of the retained three-phase rays. -/
theorem root_projective_eq_iff (r s : Coordinates) (hr : IsRoot r) (hs : IsRoot s) :
    Projectivization.mk Scalar r (root_ne_zero hr) =
      Projectivization.mk Scalar s (root_ne_zero hs) ↔ rootRay r = rootRay s := by
  rw [Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    exact (rootRay_eq_iff s r).mpr
      ⟨a, (root_scalar_iff s hs a).mp (ha.symm ▸ hr), ha.symm⟩
  · intro h
    obtain ⟨a, _, ha⟩ := (rootRay_eq_iff s r).mp h
    exact ⟨a, ha.symm⟩

def displayedRayRepresentative (R : DisplayedReflectingRay) : Coordinates :=
  reflectingRootParameterVector R.property.choose

theorem displayedRayRepresentative_root (R : DisplayedReflectingRay) :
    IsRoot (displayedRayRepresentative R) :=
  (reflectingRootParameter_isReflectingRoot R.property.choose).1

theorem displayedRayRepresentative_ray (R : DisplayedReflectingRay) :
    rootRay (displayedRayRepresentative R) = R.val := R.property.choose_spec

/-- The normalized reflecting ray determines its actual one-dimensional
projective direction in the original coefficient space. -/
def displayedRayProjectiveDirection (R : DisplayedReflectingRay) :
    Projectivization Scalar Coordinates :=
  Projectivization.mk Scalar (displayedRayRepresentative R)
    (root_ne_zero (displayedRayRepresentative_root R))

theorem displayedRayProjectiveDirection_injective :
    Function.Injective displayedRayProjectiveDirection := by
  intro R S h
  apply Subtype.ext
  have he := (root_projective_eq_iff _ _
    (displayedRayRepresentative_root R) (displayedRayRepresentative_root S)).mp h
  simpa only [displayedRayRepresentative_ray] using he

theorem displayedRayProjectiveDirection_eq_mk (R : DisplayedReflectingRay)
    (r : Coordinates) (hr : r ≠ 0) (hR : rootRay r = R.val) :
    displayedRayProjectiveDirection R = Projectivization.mk Scalar r hr := by
  apply (Projectivization.mk_eq_mk_iff' Scalar _ _ _ _).mpr
  obtain ⟨a, _, ha⟩ := (rootRay_eq_iff r (displayedRayRepresentative R)).mp
    ((displayedRayRepresentative_ray R).trans hR.symm)
  exact ⟨a, ha.symm⟩

/-- Compatibility of the actual scalar quotient ray action with the projective
map induced by the faithful linear triple-cover representation. -/
theorem displayedRayProjectiveDirection_equivariant
    (g : rootGeneratedAlgebraParity.ker) (R : DisplayedReflectingRay) :
    displayedRayProjectiveDirection (rootGeneratedPositiveProjection g • R) =
      Projectivization.map (positiveAlgebraLinearRepresentation g).toLinearMap
        (positiveAlgebraLinearRepresentation g).injective (displayedRayProjectiveDirection R) := by
  conv_rhs => rw [displayedRayProjectiveDirection, Projectivization.map_mk]
  apply displayedRayProjectiveDirection_eq_mk
  change rootRay (g.val.val.val (displayedRayRepresentative R)) =
    (semilinearDisplayedRayMap g.val.val R).val
  rw [← semilinearAlgebra_rootRay_map, displayedRayRepresentative_ray]
  rfl

/-- Thus the induced projective map on the distinguished directions depends
only on the actual positive ray quotient element. -/
theorem displayedRayProjectiveDirection_lift_independent
    (g h : rootGeneratedAlgebraParity.ker)
    (he : rootGeneratedPositiveProjection g = rootGeneratedPositiveProjection h)
    (R : DisplayedReflectingRay) :
    Projectivization.map (positiveAlgebraLinearRepresentation g).toLinearMap
      (positiveAlgebraLinearRepresentation g).injective (displayedRayProjectiveDirection R) =
    Projectivization.map (positiveAlgebraLinearRepresentation h).toLinearMap
      (positiveAlgebraLinearRepresentation h).injective (displayedRayProjectiveDirection R) := by
  rw [← displayedRayProjectiveDirection_equivariant,
    ← displayedRayProjectiveDirection_equivariant, he]

end Atlas.Fischer
