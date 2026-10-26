import Atlas.Rudvalis.SignKernel
import Atlas.Rudvalis.TorsionMinimum

/-! Local row geometry of the heavy seed support; certificates concern one eight-point row. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def heavySupportBit (r : Fin 7) (k : Fin 8) : Bit :=
  (signedPositionSign k * seedBArray (r,signedPositionIndex k) : ℤ)

def heavyRowRepresentative (r : Fin 7) : Fin 8 := ![0,0,0,4,0,2,2] r

noncomputable def heavySeedResidue : BinaryWord := fun z => (seedBWord z : Bit)

theorem heavySeedResidue_mem : heavySeedResidue∈binaryResidue := seedB_residue_mem

theorem heavySeedResidue_apply (r : Fin 7) (k : Fin 8) :
    heavySeedResidue (seedCoordinateEquiv (r,k))=heavySupportBit r k := by
  exact congrArg (fun n : ℤ => (n : Bit)) (signedSeedTransport_apply seedBArray r k)

theorem heavySupport_representative (r : Fin 7) : heavySupportBit r (heavyRowRepresentative r)=1 := by
  decide +kernel +revert

def heavyMomentTest (i : Fin 2) : BinaryWord := binaryNormalMap
  (0,outerMatrix (if i=0 then binaryLabel 1 else binaryLabel 6) (binaryLabel 2),0)

def heavyMomentRow (i : Fin 2) (r : Fin 7) (k : Fin 8) : Bit :=
  heavyMomentTest i (rowLabel r,seedInnerLabel r k)

theorem heavyMomentTest_mem (i : Fin 2) : heavyMomentTest i∈binaryResidue := ⟨_,rfl⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem heavySupport_nonheavy_row (r : Fin 7) (hr : r≠0) (f : Fin 8→Bit)
    (hs : ∀ k, heavySupportBit r k=0 → f k=0) (hp : ∑k,f k=0) :
    ∀ k, f k=f (heavyRowRepresentative r)*heavySupportBit r k := by
  decide +kernel +revert

theorem heavySupport_other_moment (i : Fin 2) (r : Fin 7) (hr : r≠0) :
    (∑k,heavyMomentRow i r k*heavySupportBit r k)=0 := by
  decide +kernel +revert

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem heavySupport_heavy_row (f : Fin 8→Bit)
    (hs : ∀ k, heavySupportBit 0 k=0 → f k=0) (hp : ∑k,f k=0)
    (hm : ∀ i : Fin 2, (∑k,heavyMomentRow i 0 k*f k)=0) :
    ∀ k, f k=f (heavyRowRepresentative 0)*heavySupportBit 0 k := by
  decide +kernel +revert

theorem heavySupport_first_moment (r : Fin 7) :
    (∑ k,seedInnerLabel r k 1*heavySupportBit r k)=1 := by
  decide +kernel +revert

end Atlas.Rudvalis
