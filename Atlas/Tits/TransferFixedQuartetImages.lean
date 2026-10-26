import Atlas.Tits.TransferWitnessPowers
import Atlas.Tits.FiveQuartetMultiplierProperties

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary
set_option maxRecDepth 16384

/-- The witness fixes the second member of the reference couple. -/
theorem localCodeAlpha_fixes_second : localCodeAlpha • referenceSecondCross = referenceSecondCross := by
  rw [referenceSecondCross_eq, coordinateCross_action]
  have h := congrArg (fun g : binaryPermutationGroup => g.val (rowLabel 0,binaryLabel 2))
    localCodeAlpha_translation
  change localCodeAlpha.val.right (rowLabel 0,binaryLabel 2) =
    coordinateTranslation alphaTranslationMatrix (rowLabel 0,binaryLabel 2) at h
  rw [h,coordinateCross_eq_iff,codeI_coordinate]
  decide +kernel

noncomputable def pairAlphaCode : codeCoupleStabilizer :=
  ⟨localCodeAlpha,pointAlpha.prop,localCodeAlpha_fixes_second⟩
noncomputable def pairAlpha : pairStabilizer := codePairHom pairAlphaCode

theorem pairAlpha_underlying : pairAlpha.val = localAlpha := rfl

theorem localAlpha_fixes_referenceNeighbour : localAlpha • referenceNeighbour = referenceNeighbour :=
  pairAlpha.prop

/-- Intrinsic exhaustion places every reference-couple quartet in the original frame. -/
theorem fiveQuartet_subset_coordinateFrame (Q : FiveQuartets) : Q.val ⊆ coordinateFrame := by
  intro c hc
  apply referenceCoordinateDozen_subset
  rw [← reference_intrinsicDozen_eq]
  exact ⟨Q.val,Q.prop.1,Q.prop.2,hc⟩

/-- Any pair-group element whose square fixes all original frame crosses has
 square-trivial action on the actual five quartets. -/
theorem fiveQuartet_square_of_coordinate_fixed (g : pairStabilizer)
    (hg : ∀ i : Coordinate, (g^2).val.val • coordinateCross i = coordinateCross i) :
    fiveQuartetHom g ^ 2 = 1 := by
  apply Equiv.ext
  intro Q
  rw [fiveQuartetHom_pow_apply]
  change g^2 • Q = Q
  apply Subtype.ext
  change (fun c : MinimalCross => (g^2).val.val • c) '' Q.val = Q.val
  calc
    _ = id '' Q.val := Set.image_congr (by
      intro c hc
      obtain ⟨i,rfl⟩ := coordinateFrame_rep c (fiveQuartet_subset_coordinateFrame Q hc)
      exact hg i)
    _ = Q.val := Set.image_id _

theorem pairAlpha_image_square : fiveQuartetHom pairAlpha ^ 2 = 1 := by
  apply fiveQuartet_square_of_coordinate_fixed
  intro i
  rw [pairAlpha,codePair_power_cross]
  change localCodeAlpha^2 • coordinateCross i = coordinateCross i
  rw [localCodeAlpha_square,coordinateCross_action]
  rfl

theorem alphaPlane_coordinate_not_mem :
    coordinateCross (coordinateTranslation alphaTranslationMatrix (originalCoordinateEquiv (4,0))) ∉
      betaPlaneQuartet.val := by
  let i := coordinateTranslation alphaTranslationMatrix (originalCoordinateEquiv (4,0))
  have hr : i.1 = rowLabel 4 := rfl
  have hd : dot referencePlaneNormal.val i.2 = 1 := by decide +kernel
  have he : i = (rowLabel 4,i.2) := Prod.ext hr rfl
  change coordinateCross i ∉ coordinatePlaneQuartet (rowLabel 0) (rowLabel 4) referencePlaneNormal 0 0
  rw [he]
  rintro (h|h)
  · have hh := coordinatePlaneSlice_subset _ _ _ h
    have hn := (coordinateCross_mem_row_iff _ _ _).mp hh
    exact (by decide +kernel : rowLabel 4 ≠ rowLabel 0) hn.symm
  · have hh := (coordinatePlaneSlice_mem _ _ (by decide +kernel) 0 i.2).mp h
    rw [hd] at hh
    exact one_ne_zero hh

theorem pairAlpha_image_ne_one : fiveQuartetHom pairAlpha ≠ 1 := by
  intro h
  have he := congrArg (fun f : Equiv.Perm FiveQuartets => f betaPlaneQuartet) h
  change pairAlpha • betaPlaneQuartet = betaPlaneQuartet at he
  have hm : coordinateCross (localCodeAlpha.val.right (originalCoordinateEquiv (4,0))) ∈
      (pairAlpha • betaPlaneQuartet).val := by
    refine ⟨coordinateCross (originalCoordinateEquiv (4,0)),betaPlane_initial_coordinate,?_⟩
    dsimp only
    change codeGaussianHom localCodeAlpha • coordinateCross _ = _
    rw [codeGaussianHom_cross,coordinateCross_action]
  rw [he] at hm
  have hc := congrArg (fun g : binaryPermutationGroup => g.val (originalCoordinateEquiv (4,0)))
    localCodeAlpha_translation
  change localCodeAlpha.val.right _ = coordinateTranslation alphaTranslationMatrix _ at hc
  rw [hc] at hm
  exact alphaPlane_coordinate_not_mem hm

/-- The first actual fixed neighbour contributes minus one to the transfer. -/
theorem pairAlpha_multiplier : fiveQuartetMultiplier pairAlpha = -1 := by
  apply fiveQuartetImageMultiplier_involution (fiveQuartetHom.rangeRestrict pairAlpha)
  · apply Subtype.ext
    exact pairAlpha_image_square
  · intro h
    exact pairAlpha_image_ne_one (congrArg Subtype.val h)

end Atlas.Tits
