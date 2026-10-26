import Atlas.Rudvalis.CoupleMonomialGenerators
import Atlas.Rudvalis.FourSupportCount

/-! The six (form, active-constant parity) states, represented by the 24
actual odd affine-support choices on the three forms orthogonal to row 0. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def coupleFourForm (a : Fin 3) : E := binaryLabel (![1,6,7] a)
def coupleFourActiveRow (a : Fin 3) (j : Fin 4) : Fin 7 :=
  ![![1,2,3,6],![2,4,5,6],![1,3,4,5]] a j

def coupleFourRowConstants (a : Fin 3) (m : E) (r : Fin 7) : Bit :=
  if r=coupleFourActiveRow a 0 then m 0 else
  if r=coupleFourActiveRow a 1 then m 1 else
  if r=coupleFourActiveRow a 2 then m 2 else
  if r=coupleFourActiveRow a 3 then 1+m 0+m 1+m 2 else 0

noncomputable def coupleFourConstants (a : Fin 3) (m : E) (p : Point) : Bit :=
  coupleFourRowConstants a m (rowEquiv.symm p)

noncomputable def coupleFourSupport (a : Fin 3) (m : E) : BinaryWord :=
  binaryNormalMap (coupleFourConstants a m,outerMatrix (coupleFourForm a) (coupleFourForm a),0)

def coupleFourOriginalSupport (a : Fin 3) (m : E) (z : SeedCoordinate) : Bit :=
  coupleFourRowConstants a m z.1+dot (coupleFourForm a) (rowLabel z.1).val*
    dot (coupleFourForm a) (seedInnerLabel z.1 (signedPositionIndex z.2))

theorem coupleFourConstants_rows (a : Fin 3) (m : E) (r : Fin 7) :
    coupleFourConstants a m (rowLabel r)=coupleFourRowConstants a m r := by
  change coupleFourRowConstants a m (rowEquiv.symm (rowEquiv r))=_
  rw [rowEquiv.symm_apply_apply]

theorem coupleFourSupport_original (a : Fin 3) (m : E) (z : SeedCoordinate) :
    coupleFourSupport a m (originalCoordinateEquiv z)=coupleFourOriginalSupport a m z := by
  change coupleFourConstants a m (rowLabel z.1)+
    dot (matrixAt (outerMatrix (coupleFourForm a) (coupleFourForm a)) (rowLabel z.1).val)
      (seedInnerLabel z.1 (signedPositionIndex z.2))+
    theta (rowLabel z.1) 0 (seedInnerLabel z.1 (signedPositionIndex z.2))=_
  rw [coupleFourConstants_rows,matrixAt_outer,dot_smul_left,theta_zero_parameter,add_zero]
  rfl

theorem coupleFourRowConstants_valid (a : Fin 3) (m : E) :
    (∀r,dot (coupleFourForm a) (rowLabel r).val=0 → coupleFourRowConstants a m r=0) ∧
    (∑r,coupleFourRowConstants a m r)=1 := by decide +kernel +revert

theorem coupleFourConstants_valid (a : Fin 3) (m : E) :
    (∀p,dot (coupleFourForm a) p.val=0 → coupleFourConstants a m p=0) ∧
    (∑p,coupleFourConstants a m p)=1 := by
  constructor
  · intro p hp
    obtain ⟨r,rfl⟩ := rowLabel_bijective.2 p
    rw [coupleFourConstants_rows]
    exact (coupleFourRowConstants_valid a m).1 r hp
  · rw [←Equiv.sum_comp rowEquiv]
    simp_rw [show ∀r,coupleFourConstants a m (rowEquiv r)=coupleFourRowConstants a m r from
      coupleFourConstants_rows a m]
    exact (coupleFourRowConstants_valid a m).2

/-- 0=R and 1=beta. -/
noncomputable def coupleOriginalGenerator (b : Fin 2) : SignedCoordinates SeedCoordinate :=
  if b=0 then seedRMonomial else coupleOriginalBeta
noncomputable def coupleCodeGenerator (b : Fin 2) : codeGroup :=
  if b=0 then codeR else coupleCodeBeta

def coupleFourTransportForm (a : Fin 3) : Fin 3 := ![0,2,1] a

noncomputable def coupleFourTransportParameters (b : Fin 2) (a : Fin 3) (m : E) : E :=
  fun j => coupleFourOriginalSupport a m ((coupleOriginalGenerator b).right.symm
    (coupleFourActiveRow (coupleFourTransportForm a) ⟨j.val,by omega⟩,1))

theorem coupleFour_original_transport (b : Fin 2) (a : Fin 3) (m : E) (z : SeedCoordinate) :
    coupleFourOriginalSupport a m ((coupleOriginalGenerator b).right.symm z)=
      coupleFourOriginalSupport (coupleFourTransportForm a) (coupleFourTransportParameters b a m) z := by
  decide +kernel +revert

def coupleFourParity (a : Fin 3) (m : E) : Bit :=
  coupleFourRowConstants a m (![1,5,1] a)+coupleFourRowConstants a m (![3,4,3] a)

def coupleFourState (a : Fin 3) (m : E) : Fin 6 :=
  ⟨2*a.val+(coupleFourParity a m).val,by
    have h := ZMod.val_lt (coupleFourParity a m)
    have ha := a.isLt
    omega⟩

def coupleSixStatePermutation (b : Fin 2) (s : Fin 6) : Fin 6 :=
  if b=0 then ![0,1,4,5,2,3] s else ![1,0,5,4,2,3] s

theorem coupleFour_six_state_action (b : Fin 2) (a : Fin 3) (m : E) :
    coupleFourState (coupleFourTransportForm a) (coupleFourTransportParameters b a m)=
      coupleSixStatePermutation b (coupleFourState a m) := by
  decide +kernel +revert

end Atlas.Rudvalis
