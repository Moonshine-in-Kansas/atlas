import Atlas.Lattices.EisensteinComparisonSpace

namespace Atlas.Lattices
open Atlas.Algebra

/-- The scalar omega action transported to the retained rational Leech space. -/
noncomputable def eisensteinRationalRotation :
    RationalCoordinates ≃ₗ[ℚ] RationalCoordinates :=
  eisensteinComparison.symm.trans (eisensteinRotationEquiv.trans eisensteinComparison)

@[simp] theorem eisensteinRationalRotation_apply (x : RationalCoordinates) :
    eisensteinRationalRotation x =
      eisensteinComparison (eisensteinRotation (eisensteinComparison.symm x)) := rfl

/-- The transported scalar satisfies its defining quadratic polynomial. -/
theorem eisensteinRationalRotation_polynomial (x : RationalCoordinates) :
    eisensteinRationalRotation (eisensteinRationalRotation x) +
      eisensteinRationalRotation x + x = 0 := by
  have h := congrArg eisensteinComparison
    (eisensteinRotation_polynomial (eisensteinComparison.symm x))
  simpa only [map_add, map_zero, eisensteinRationalRotation_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] using h

/-- The transported scalar has cube one. -/
theorem eisensteinRationalRotation_cube (x : RationalCoordinates) :
    eisensteinRationalRotation (eisensteinRationalRotation (eisensteinRationalRotation x)) = x := by
  simp only [eisensteinRationalRotation_apply, LinearEquiv.symm_apply_apply,
    eisensteinRotation_cube, LinearEquiv.apply_symm_apply]

/-- It has no nonzero rational fixed vectors. -/
theorem eisensteinRationalRotation_fixed_iff (x : RationalCoordinates) :
    eisensteinRationalRotation x = x ↔ x = 0 := by
  constructor
  · intro h
    have hr : eisensteinRotation (eisensteinComparison.symm x) =
        eisensteinComparison.symm x :=
      eisensteinComparison.injective (h.trans (eisensteinComparison.apply_symm_apply x).symm)
    have hz := (eisensteinRotation_fixed_iff _).mp hr
    have hx := congrArg eisensteinComparison hz
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using hx
  · rintro rfl; exact eisensteinRationalRotation.map_zero

/-- The transported scalar preserves the retained rational Leech form. -/
theorem eisensteinRationalRotation_form (x y : RationalCoordinates) :
    rationalForm (eisensteinRationalRotation x) (eisensteinRationalRotation y) =
      rationalForm x y := by
  rw [eisensteinRationalRotation_apply, eisensteinRationalRotation_apply,
    eisensteinComparison_isometry]
  change eisensteinReal (eisensteinHermitian
    (eisensteinRotation (eisensteinComparison.symm x))
    (eisensteinRotation (eisensteinComparison.symm y))) = _
  rw [eisensteinRotation_preserves_hermitian]
  change eisensteinBilinear (eisensteinComparison.symm x) (eisensteinComparison.symm y) = _
  simpa only [LinearEquiv.apply_symm_apply] using
    (eisensteinComparison_isometry
      (eisensteinComparison.symm x) (eisensteinComparison.symm y)).symm

end Atlas.Lattices
