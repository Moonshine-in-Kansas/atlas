import Atlas.Rudvalis.LocalBridgeQuartetObstructions
import Atlas.Rudvalis.SeedResidueParameters

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

def localBridgeDoubleArray (c : Fin 3) (j : SeedCoordinate) : ℤ :=
  (![![![0,0,0,0,0,0,0,0],![0,1,0,1,-1,0,1,0],![0,-1,1,0,-1,0,0,-1],![1,0,1,0,1,0,1,0],![0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0],![0,-1,-1,0,0,-1,1,0]],![![0,0,0,0,0,0,0,0],![0,1,1,0,0,1,-1,0],![0,0,0,0,0,0,0,0],![0,1,0,1,-1,0,1,0],![0,1,-1,0,1,0,0,1],![1,0,1,0,1,0,1,0],![0,0,0,0,0,0,0,0]],![![0,0,0,0,0,-1,-1,0],![0,0,0,0,0,1,0,-1],![0,0,1,0,0,0,0,-1],![0,0,1,0,1,0,0,0],![0,-1,0,0,0,-1,0,0],![0,-1,0,-1,0,-1,1,0],![0,0,0,-1,1,0,0,0]]] c j.1 j.2)

def localBridgeParameterCode (c : Fin 3) : ℕ := ![149,65481,172810] c

noncomputable def localBridgeDouble (c : Fin 3) : IntegerCoordinates :=
  signedSeedTransport (localBridgeDoubleArray c)

noncomputable def localBridgeWord (c : Fin 3) : QuaternaryWord := reduceModFour (localBridgeDouble c)

theorem localBridgeDouble_first (j : SeedCoordinate) :
    localExtraNumerator 8 0 j=128*localBridgeDoubleArray 0 j := by decide +kernel +revert

theorem localBridgeDouble_middle (j : SeedCoordinate) :
    seedP5Array j=localBridgeDoubleArray 1 j := by decide +kernel +revert

theorem localBridgeDouble_last (j : SeedCoordinate) :
    localExtraNumerator 8 1 j=256*localBridgeDoubleArray 2 j := by decide +kernel +revert

theorem localBridgeDouble_apply (c : Fin 3) (r : Fin 7) (k : Fin 8) :
    localBridgeDouble c (seedCoordinateEquiv (r,k))=
      signedPositionSign k*localBridgeDoubleArray c (r,signedPositionIndex k) :=
  signedSeedTransport_apply _ r k

theorem localBridgeWord_apply (c : Fin 3) (r : Fin 7) (k : Fin 8) :
    localBridgeWord c (seedCoordinateEquiv (r,k))=
      ((signedPositionSign k*localBridgeDoubleArray c (r,signedPositionIndex k):ℤ):ZMod 4) :=
  congrArg (fun z : ℤ => (z:ZMod 4)) (localBridgeDouble_apply c r k)

theorem localBridgeWord_residue (c : Fin 3) :
    reduce (localBridgeWord c)=binaryNormalMap (seedEncodedParameters (localBridgeParameterCode c)) := by
  funext i
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective i
  change reduceScalar (localBridgeWord c (seedCoordinateEquiv (r,k)))=_
  rw [localBridgeWord_apply]
  change reduceScalar (((signedPositionSign k*localBridgeDoubleArray c (r,signedPositionIndex k):ℤ):ZMod 4))=
    binaryNormalMap (seedEncodedParameters (localBridgeParameterCode c)) (rowLabel r,seedInnerLabel r k)
  decide +kernel +revert

theorem localBridgeWord_balanced (c : Fin 3) : integerLift (localBridgeWord c)=localBridgeDouble c := by
  funext i
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective i
  change integerRepresentative (localBridgeWord c (seedCoordinateEquiv (r,k)))=_
  rw [localBridgeWord_apply,localBridgeDouble_apply]
  decide +kernel +revert

theorem localBridgeWord_weight (c : Fin 3) : euclideanWeight (localBridgeWord c)=16 := by
  rw [euclideanWeight,←Equiv.sum_comp seedCoordinateEquiv]
  change (∑j : SeedCoordinate,euclideanSymbolWeight (localBridgeWord c (seedCoordinateEquiv j)))=16
  simp_rw [show ∀j : SeedCoordinate,localBridgeWord c (seedCoordinateEquiv j)=
    (((signedPositionSign j.2*localBridgeDoubleArray c (j.1,signedPositionIndex j.2)):ℤ):ZMod 4) from fun j=>localBridgeWord_apply c j.1 j.2]
  decide +kernel +revert

end Atlas.Rudvalis
