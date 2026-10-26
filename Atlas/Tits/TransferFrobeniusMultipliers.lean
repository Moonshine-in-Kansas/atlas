import Atlas.Tits.TransferFixedQuartetImages
import Atlas.Rudvalis.FourLocalLabels

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary
set_option maxRecDepth 16384

noncomputable def alphaFrobeniusCode (n : Fin 3) : codeGroup :=
  (codeT^n.val)⁻¹ * localCodeAlpha * codeT^n.val
noncomputable def alphaFrobeniusOriginal (n : Fin 3) : SignedCoordinates SeedCoordinate :=
  (seedTMonomial^n.val)⁻¹ * localOriginalAlpha * seedTMonomial^n.val

theorem alphaFrobenius_transport (n : Fin 3) :
    (alphaFrobeniusCode n).val = seedConjugateHom (alphaFrobeniusOriginal n) := by
  change ((codeT.val^n.val)⁻¹ * localCodeAlpha.val) * codeT.val^n.val = _
  rw [localCodeAlpha_transport]
  change ((seedConjugateHom seedTMonomial)^n.val)⁻¹ * seedConjugateHom localOriginalAlpha *
    (seedConjugateHom seedTMonomial)^n.val = _
  simp only [alphaFrobeniusOriginal,map_mul,map_inv,map_pow]

set_option maxHeartbeats 2000000 in
-- Three conjugates on two marked coordinate axes, not a full shell certificate.
theorem alphaFrobenius_pair_coordinates (n : Fin 3) (k : Fin 8) (hk : k=1 ∨ k=2) :
    (alphaFrobeniusOriginal n).right (0,k) = (0,k) ∨
      (alphaFrobeniusOriginal n).right (0,k) = (seedUnitMonomial 4).right (0,k) := by
  decide +kernel +revert

theorem alphaFrobenius_fixes_first (n : Fin 3) :
    alphaFrobeniusCode n • localReferenceCross = localReferenceCross := by
  have he : localReferenceCross = coordinateCross (originalCoordinateEquiv (0,1)) := by
    rw [localReferenceCross_eq]
    congr 1
    decide +kernel
  rw [he]
  exact original_coordinate_cross_fix_at _ _ (alphaFrobenius_transport n) _
    (alphaFrobenius_pair_coordinates n 1 (Or.inl rfl))

theorem alphaFrobenius_fixes_second (n : Fin 3) :
    alphaFrobeniusCode n • referenceSecondCross = referenceSecondCross := by
  have he : referenceSecondCross = coordinateCross (originalCoordinateEquiv (0,2)) := by
    rw [referenceSecondCross_eq]
    congr 1
  rw [he]
  exact original_coordinate_cross_fix_at _ _ (alphaFrobenius_transport n) _
    (alphaFrobenius_pair_coordinates n 2 (Or.inr rfl))

noncomputable def alphaFrobeniusPairCode (n : Fin 3) : codeCoupleStabilizer :=
  ⟨alphaFrobeniusCode n,alphaFrobenius_fixes_first n,alphaFrobenius_fixes_second n⟩
noncomputable def alphaFrobeniusPair (n : Fin 3) : pairStabilizer :=
  codePairHom (alphaFrobeniusPairCode n)

theorem alphaFrobenius_square (n : Fin 3) :
    alphaFrobeniusCode n ^ 2 =
      (codeT^n.val)⁻¹ * seedARowSign (binaryLabel 3) * codeT^n.val := by
  rw [alphaFrobeniusCode,show ((codeT^n.val)⁻¹*localCodeAlpha*codeT^n.val)^2 =
    (codeT^n.val)⁻¹*localCodeAlpha^2*codeT^n.val by simp only [pow_two,mul_assoc,mul_inv_cancel_left],localCodeAlpha_square]

theorem alphaFrobenius_image_square (n : Fin 3) :
    fiveQuartetHom (alphaFrobeniusPair n) ^ 2 = 1 := by
  apply fiveQuartet_square_of_coordinate_fixed
  intro i
  rw [alphaFrobeniusPair,codePair_power_cross]
  change alphaFrobeniusCode n ^ 2 • coordinateCross i = coordinateCross i
  rw [alphaFrobenius_square,mul_smul,mul_smul,coordinateCross_action]
  have hs : seedARowSign (binaryLabel 3) •
      coordinateCross ((codeT^n.val).val.right i) =
      coordinateCross ((codeT^n.val).val.right i) := by
    rw [coordinateCross_action]
    rfl
  rw [hs,←coordinateCross_action,inv_smul_smul]

set_option maxHeartbeats 2000000 in
-- The three transported direction-plane obstructions at one marked axis each.
theorem alphaFrobenius_plane_certificate (n : Fin 3) :
    (originalCoordinateEquiv ((alphaFrobeniusOriginal n).right (4,0))).1 = rowLabel 4 ∧
    dot referencePlaneNormal.val
      (originalCoordinateEquiv ((alphaFrobeniusOriginal n).right (4,0))).2 = 1 := by
  decide +kernel +revert

theorem alphaFrobenius_plane_not_mem (n : Fin 3) :
    coordinateCross (originalCoordinateEquiv ((alphaFrobeniusOriginal n).right (4,0))) ∉
      betaPlaneQuartet.val := by
  let i := originalCoordinateEquiv ((alphaFrobeniusOriginal n).right (4,0))
  obtain ⟨hr,hd⟩ := alphaFrobenius_plane_certificate n
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

theorem alphaFrobenius_image_ne_one (n : Fin 3) :
    fiveQuartetHom (alphaFrobeniusPair n) ≠ 1 := by
  intro h
  have he := congrArg (fun f : Equiv.Perm FiveQuartets => f betaPlaneQuartet) h
  change alphaFrobeniusPair n • betaPlaneQuartet = betaPlaneQuartet at he
  have hm : coordinateCross ((alphaFrobeniusCode n).val.right (originalCoordinateEquiv (4,0))) ∈
      (alphaFrobeniusPair n • betaPlaneQuartet).val := by
    refine ⟨coordinateCross (originalCoordinateEquiv (4,0)),betaPlane_initial_coordinate,?_⟩
    dsimp only
    change codeGaussianHom (alphaFrobeniusCode n) • coordinateCross _ = _
    rw [codeGaussianHom_cross,coordinateCross_action]
  rw [he,alphaFrobenius_transport] at hm
  change coordinateCross ((seedConjugateMonomial (alphaFrobeniusOriginal n)).right
    (originalCoordinateEquiv (4,0))) ∈ _ at hm
  rw [seedConjugateMonomial_right,original_congr_apply] at hm
  exact alphaFrobenius_plane_not_mem n hm

/-- All three Frobenius-transported fixed-neighbour multipliers are minus one. -/
theorem alphaFrobenius_multiplier (n : Fin 3) :
    fiveQuartetMultiplier (alphaFrobeniusPair n) = -1 := by
  apply fiveQuartetImageMultiplier_involution
    (fiveQuartetHom.rangeRestrict (alphaFrobeniusPair n))
  · apply Subtype.ext
    exact alphaFrobenius_image_square n
  · intro h
    exact alphaFrobenius_image_ne_one n (congrArg Subtype.val h)

noncomputable def pointFrobenius : codeReferenceStabilizer := ⟨codeT,by
  have he : localReferenceCross = coordinateCross (originalCoordinateEquiv (0,1)) := by
    rw [localReferenceCross_eq]
    congr 1
    decide +kernel
  change codeT • localReferenceCross = localReferenceCross
  rw [he]
  exact codeT_local_fix⟩

noncomputable def localFrobenius : Ambient := codePointHom pointFrobenius

/-- The three local five-set computations use genuine transporters in J. -/
theorem alphaFrobeniusPair_underlying (n : Fin 3) :
    (alphaFrobeniusPair n).val =
      (localFrobenius^n.val)⁻¹ * localAlpha * localFrobenius^n.val := by
  change codePointHom ⟨alphaFrobeniusCode n,alphaFrobenius_fixes_first n⟩ = _
  rw [localFrobenius,localAlpha,←map_pow,←map_inv,←map_mul,←map_mul]
  congr 1

noncomputable def alphaFixedNeighbour (n : Fin 3) : Neighbours :=
  localFrobenius^n.val • referenceNeighbour

theorem alphaFixedNeighbour_fixed (n : Fin 3) :
    localAlpha • alphaFixedNeighbour n = alphaFixedNeighbour n := by
  have h := (alphaFrobeniusPair n).prop
  change (alphaFrobeniusPair n).val • referenceNeighbour = referenceNeighbour at h
  rw [alphaFrobeniusPair_underlying,mul_smul,mul_smul] at h
  have hh := congrArg (fun v : Neighbours => localFrobenius^n.val • v) h
  simpa only [smul_inv_smul,alphaFixedNeighbour] using hh

end Atlas.Tits

