import Atlas.Rudvalis.LocalBridgeShellPieces
import Atlas.Rudvalis.CrossRowEnergy

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators
set_option maxRecDepth 6000

theorem localBridgeWord_coupleZero (c : Fin 3) : HeavyCoupleZero (reduce (localBridgeWord c)) := by
  rw [localBridgeWord_residue]
  unfold HeavyCoupleZero
  decide +kernel +revert

theorem localBridgeShell_common (c : Fin 3) :
    ReferenceCoupleOrthogonal (minimalCross (localBridgeShell c)) := by
  rw [ReferenceCoupleOrthogonal,localReferenceCross_eq,referenceSecondCross_eq,
    ←localBridgeMinimumWord_shell]
  have hp (p : Point) (x : E) :
      CrossOrthogonal (coordinateCross (p,x)) (minimalCross (minimumWordShellLift (localBridgeMinimumWord c))) ↔
        reduce (localBridgeWord c) (p,x)=0 ∧ reduce (localBridgeWord c) (p,x+p.val)=0 := by
    rw [coordinateCross,crossOrthogonal_mk]
    change HermitianOrthogonal (coordinateMinimum (p,x))
      (minimumWordShellLift (localBridgeMinimumWord c)).val.val ↔ _
    rw [coordinate_hermitianOrthogonal_pair,minimumWordShellLift_zero_iff,minimumWordShellLift_zero_iff]
    rfl
  rw [hp,hp]
  exact localBridgeWord_coupleZero c

theorem localBridgeDouble_selected_square (c : Fin 3) :
    (∑j : SeedCoordinate,if dot (binaryLabel 1) (rowLabel j.1).val=0 then
      (signedPositionSign j.2*localBridgeDoubleArray c (j.1,signedPositionIndex j.2))^2 else 0)=
        (![0,8,8] c : ℤ) := by
  decide +kernel +revert

theorem localBridgeShell_energy (c : Fin 3) :
    coordinateRowEnergy referenceDozenRows (localBridgeShell c).val.val=![0,2,2] c := by
  classical
  rw [localBridgeShell_val,coordinateRowEnergy_half,←Equiv.sum_comp seedCoordinateEquiv]
  have hs : (∑j : SeedCoordinate,if (seedCoordinateEquiv j).1∈referenceDozenRows then
      ((localBridgeDouble c (seedCoordinateEquiv j):ℤ):ℚ)^2 else 0)=
      ((![0,8,8] c : ℤ):ℚ) := by
    simp_rw [show ∀j : SeedCoordinate,localBridgeDouble c (seedCoordinateEquiv j)=
      signedPositionSign j.2*localBridgeDoubleArray c (j.1,signedPositionIndex j.2) from
        fun j=>localBridgeDouble_apply c j.1 j.2]
    have hp (j : SeedCoordinate) : (seedCoordinateEquiv j).1∈referenceDozenRows ↔
        dot (binaryLabel 1) (rowLabel j.1).val=0 := Iff.rfl
    simp_rw [hp]
    exact_mod_cast localBridgeDouble_selected_square c
  rw [hs]
  fin_cases c <;> norm_num

theorem localBridgeCross_energy (c : Fin 3) :
    crossRowEnergy referenceDozenRows (minimalCross (localBridgeShell c))=![0,2,2] c :=
  localBridgeShell_energy c

theorem localFourBridgeCross_common : ReferenceCoupleOrthogonal localFourBridgeCross :=
  localBridgeShell_common 0

theorem shiftedSeedCross_common : ReferenceCoupleOrthogonal shiftedSeedCross :=
  localBridgeShell_common 1

theorem localHeavyBridgeCross_common : ReferenceCoupleOrthogonal localHeavyBridgeCross :=
  localBridgeShell_common 2

theorem localFourBridgeCross_energy : crossRowEnergy referenceDozenRows localFourBridgeCross=0 :=
  localBridgeCross_energy 0

theorem shiftedSeedCross_energy : crossRowEnergy referenceDozenRows shiftedSeedCross=2 :=
  localBridgeCross_energy 1

theorem localHeavyBridgeCross_energy : crossRowEnergy referenceDozenRows localHeavyBridgeCross=2 :=
  localBridgeCross_energy 2

end Atlas.Rudvalis
