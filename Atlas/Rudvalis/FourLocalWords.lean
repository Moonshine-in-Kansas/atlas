import Atlas.Rudvalis.CoordinateCrossLocalAction
import Atlas.Rudvalis.SeedAFibreOrbit

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
set_option maxRecDepth 16384

noncomputable def fourLocalSeed : SeedCoordinate → ZMod 4 :=
  monomialHom (seedPMonomial^3) (fun z => (seedAArray z : ZMod 4))
noncomputable def fourLocalOriginalZ : SignedCoordinates SeedCoordinate :=
  seedPMonomial^3*seedRMonomial*seedUnitMonomial 2*seedPMonomial^4
noncomputable def fourLocalCodeZ : codeGroup := codeP^3*codeR*codeSigma*codeP^4
noncomputable def fourLocalOriginalA : SignedCoordinates SeedCoordinate := seedAOriginalU 4*seedAOriginalU 5
noncomputable def fourLocalCodeA : codeGroup := seedACodeU 4*seedACodeU 5
noncomputable def fourLocalOriginalB : SignedCoordinates SeedCoordinate :=
  seedUnitMonomial 4*seedAOriginalU 6*seedUnitMonomial 1*seedAOriginalU 1
noncomputable def fourLocalCodeB : codeGroup := codeI*seedACodeU 6*codeRho*seedACodeU 1

 theorem fourLocalCodeZ_transport : fourLocalCodeZ.val=seedConjugateHom fourLocalOriginalZ := by
  simp only [fourLocalCodeZ,fourLocalOriginalZ,map_mul,map_pow,Subgroup.coe_mul,Subgroup.coe_pow]
  rfl
 theorem fourLocalCodeA_transport : fourLocalCodeA.val=seedConjugateHom fourLocalOriginalA := by
  simp only [fourLocalCodeA,fourLocalOriginalA,map_mul,Subgroup.coe_mul,seedACodeU_transport]
 theorem fourLocalCodeB_transport : fourLocalCodeB.val=seedConjugateHom fourLocalOriginalB := by
  simp only [fourLocalCodeB,fourLocalOriginalB,map_mul,Subgroup.coe_mul,seedACodeU_transport]
  rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16384 in
theorem fourLocalOriginal_fix :
    (fourLocalOriginalZ.right (0,1)=(0,1) ∨ fourLocalOriginalZ.right (0,1)=(0,0)) ∧
    (fourLocalOriginalA.right (0,1)=(0,1) ∨ fourLocalOriginalA.right (0,1)=(0,0)) ∧
    (fourLocalOriginalB.right (0,1)=(0,1) ∨ fourLocalOriginalB.right (0,1)=(0,0)) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16384 in
theorem fourLocalOriginal_sign_support (z : SeedCoordinate) :
    reduceScalar (monomialHom fourLocalOriginalA fourLocalSeed z)=reduceScalar (fourLocalSeed z) ∧
    reduceScalar (monomialHom fourLocalOriginalB fourLocalSeed z)=reduceScalar (fourLocalSeed z) := by
  decide +kernel +revert

def fourLocalMask (m : ℕ) (z : SeedCoordinate) : Bit :=
  if dot (binaryLabel 1) (rowLabel z.1).val=1 then
    (m / 2^z.1.val : ℕ)+dot (binaryLabel 1) (seedInnerLabel z.1 (signedPositionIndex z.2)) else 0

set_option maxHeartbeats 2000000 in
theorem fourLocalOriginal_support_masks (z : SeedCoordinate) :
    reduceScalar (fourLocalSeed z)=fourLocalMask 70 z ∧
    reduceScalar (monomialHom fourLocalOriginalZ fourLocalSeed z)=fourLocalMask 64 z := by
  decide +kernel +revert

theorem original_coordinate_cross_fix (g : codeGroup) (h : SignedCoordinates SeedCoordinate)
    (hg : g.val=seedConjugateHom h)
    (hh : h.right (0,1)=(0,1) ∨ h.right (0,1)=(0,0)) :
    g • coordinateCross (originalCoordinateEquiv (0,1))=coordinateCross (originalCoordinateEquiv (0,1)) := by
  rw [coordinateCross_action,hg]
  change coordinateCross ((seedConjugateMonomial h).right (originalCoordinateEquiv (0,1)))=_
  rw [seedConjugateMonomial_right,original_congr_apply]
  rcases hh with hh|hh
  · rw [hh]
  · rw [hh]
    have hi : codeI.val.right (originalCoordinateEquiv (0,1))=originalCoordinateEquiv (0,0) := by
      rw [codeI_coordinate]
      decide +kernel
    rw [←hi,coordinateCross_I]

theorem fourLocalCode_fix :
    fourLocalCodeZ • coordinateCross (originalCoordinateEquiv (0,1))=coordinateCross (originalCoordinateEquiv (0,1)) ∧
    fourLocalCodeA • coordinateCross (originalCoordinateEquiv (0,1))=coordinateCross (originalCoordinateEquiv (0,1)) ∧
    fourLocalCodeB • coordinateCross (originalCoordinateEquiv (0,1))=coordinateCross (originalCoordinateEquiv (0,1)) :=
  ⟨original_coordinate_cross_fix _ _ fourLocalCodeZ_transport fourLocalOriginal_fix.1,
   original_coordinate_cross_fix _ _ fourLocalCodeA_transport fourLocalOriginal_fix.2.1,
   original_coordinate_cross_fix _ _ fourLocalCodeB_transport fourLocalOriginal_fix.2.2⟩

end Atlas.Rudvalis
