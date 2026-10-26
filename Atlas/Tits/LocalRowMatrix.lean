import Atlas.Tits.LocalTraceSpan

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary
set_option maxRecDepth 16384

set_option maxHeartbeats 2000000 in
-- The existing order-three word is checked on the seven marked rows.
theorem originalN_row_matrix (z : SeedCoordinate) :
    (rowLabel (((coupleOriginalD ^ 4).right z).1)).val =
      matrixAt localRowMatrix (rowLabel z.1).val := by
  decide +kernel +revert

theorem codeBlockMatrix_of_original_rows (g : codeGroup)
    (a : SignedCoordinates SeedCoordinate) (M : BinaryMatrix)
    (hg : g.val = seedConjugateHom a)
    (hm : ∀ z, (rowLabel (a.right z).1).val = matrixAt M (rowLabel z.1).val) :
    binaryLinearMatrix (codeBlockLinearHom g) = M := by
  apply binaryMatrix_eq_of_apply
  intro x
  rw [binaryLinearMatrix_apply]
  by_cases hx : x = 0
  · subst x
    rw [map_zero]
    symm
    ext j
    simp [matrixAt]
  obtain ⟨r, hr⟩ := rowLabel_bijective.surjective (⟨x,hx⟩ : Point)
  have hp : (rowLabel r).val = x := congrArg Subtype.val hr
  have h := codeBlockLinear_coordinates g (originalCoordinateEquiv (r,0))
  rw [hg] at h
  change codeBlockLinearHom g (rowLabel r).val =
    ((seedConjugateMonomial a).right (originalCoordinateEquiv (r,0))).1.val at h
  rw [seedConjugateMonomial_right, original_congr_apply] at h
  change codeBlockLinearHom g (rowLabel r).val = (rowLabel (a.right (r,0)).1).val at h
  rw [hm] at h
  simpa only [hp] using h

theorem localCodeN_row_matrix :
    binaryLinearMatrix (codeBlockLinearHom (coupleCodeD ^ 4)) = localRowMatrix := by
  apply codeBlockMatrix_of_original_rows _ (coupleOriginalD ^ 4)
  · simp only [Subgroup.coe_pow, coupleCodeD_transport, map_pow]
  · exact originalN_row_matrix

end Atlas.Tits
