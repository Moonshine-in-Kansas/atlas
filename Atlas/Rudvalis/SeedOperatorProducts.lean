import Atlas.Rudvalis.SeedSignedOperators

/-! Small index-and-sign certificates for the eight signed seed operators. -/
namespace Atlas.Rudvalis
open scoped BigOperators

variable {R : Type*} [CommRing R]

def seedPairing (v w : SeedCoordinate → R) : R := ∑ z, v z*w z

theorem signedCoordinateOperator_pairing (e : Equiv.Perm SeedCoordinate)
    (s : SeedCoordinate → Bool) (v w : SeedCoordinate → R) :
    seedPairing (signedCoordinateOperator e s v) (signedCoordinateOperator e s w)=
      seedPairing v w := by
  have he (z : SeedCoordinate) : signedCoordinateOperator e s v z *
      signedCoordinateOperator e s w z =v (e z)*w (e z) := by
    change (if s z then -v (e z) else v (e z)) *
      (if s z then -w (e z) else w (e z))=_
    split <;> simp
  simp only [seedPairing]
  simp_rw [he]
  exact Equiv.sum_comp e (fun z=>v z*w z)

noncomputable def seedUnitOperator (u : Fin 8) :
    (SeedCoordinate → R) ≃ₗ[R] (SeedCoordinate → R) :=
  ![1,seedRhoOperator,seedSigmaOperator,seedSigmaOperator*seedRhoOperator,
    seedIOperator,seedIOperator*seedRhoOperator,seedIOperator*seedSigmaOperator,
    seedIOperator*(seedSigmaOperator*seedRhoOperator)] u

def seedUnitRelativeIndex (u v : Fin 8) : Fin 8 :=
  (![![0,1,2,3,4,5,6,7],![1,0,3,2,5,4,7,6],![2,3,0,1,6,7,4,5],
    ![3,2,1,0,7,6,5,4],![4,5,6,7,0,1,2,3],![5,4,7,6,1,0,3,2],
    ![6,7,4,5,2,3,0,1],![7,6,5,4,3,2,1,0]] u v)

def seedUnitRelativeNegative (u v : Fin 8) : Bool :=
  (![![false,false,false,false,false,false,false,false],
    ![true,false,false,true,true,false,false,true],
    ![true,true,false,false,true,true,false,false],
    ![true,false,true,false,true,false,true,false],
    ![true,true,true,true,false,false,false,false],
    ![false,true,true,false,true,false,false,true],
    ![false,false,true,true,true,true,false,false],
    ![false,true,false,true,true,false,true,false]] u v)


def seedUnitSource (u k : Fin 8) : Fin 8 :=
  (![![0,1,2,3,4,5,6,7],![2,3,0,1,6,7,4,5],![4,5,6,7,0,1,2,3],
    ![6,7,4,5,2,3,0,1],![1,0,3,2,5,4,7,6],![3,2,1,0,7,6,5,4],
    ![5,4,7,6,1,0,3,2],![7,6,5,4,3,2,1,0]] u k)

def seedUnitSign (u k : Fin 8) : Bool :=
  (![![false,false,false,false,false,false,false,false],
    ![true,true,false,false,false,false,true,true],
    ![true,true,true,true,false,false,false,false],
    ![true,true,false,false,true,true,false,false],
    ![true,false,true,false,true,false,true,false],
    ![false,true,true,false,true,false,false,true],
    ![false,true,false,true,true,false,true,false],
    ![false,true,true,false,false,true,true,false]] u k)

def signedBit (b : Bool) (x : R) : R := if b then -x else x

theorem signedBit_comp (a b : Bool) (x : R) : signedBit a (signedBit b x)=signedBit (a ^^ b) x := by
  cases a <;> cases b <;> simp [signedBit]

theorem seedUnit_source_involution (u k : Fin 8) : seedUnitSource u (seedUnitSource u k)=k := by
  decide +kernel +revert

theorem seedUnit_action (u : Fin 8) (w : SeedCoordinate → R) (r : Fin 7) (k : Fin 8) :
    seedUnitOperator u w (r,k)=signedBit (seedUnitSign u k) (w (r,seedUnitSource u k)) := by
  fin_cases u <;> fin_cases k <;>
    simp [seedUnitOperator,seedUnitSign,seedUnitSource,signedBit,
      seedIOperator,seedRhoOperator,seedSigmaOperator,signedCoordinateOperator,
      seedIIndexEquiv,seedRhoIndexEquiv,seedSigmaIndexEquiv,seedIIndex,seedRhoIndex,seedSigmaIndex]

theorem seedUnit_inverse_action (u : Fin 8) (w : SeedCoordinate → R) (r : Fin 7) (k : Fin 8) :
    (seedUnitOperator u).symm w (r,k)=
      signedBit (seedUnitSign u (seedUnitSource u k)) (w (r,seedUnitSource u k)) := by
  have h := seedUnit_action u ((seedUnitOperator u).symm w) r (seedUnitSource u k)
  rw [LinearEquiv.apply_symm_apply,seedUnit_source_involution] at h
  have he := congrArg (signedBit (seedUnitSign u (seedUnitSource u k))) h.symm
  rw [signedBit_comp] at he
  simpa [signedBit] using he

theorem seedUnit_relative_data (u v k : Fin 8) :
    seedUnitSource v (seedUnitSource u k)=seedUnitSource (seedUnitRelativeIndex u v) k ∧
    (seedUnitSign u (seedUnitSource u k) ^^ seedUnitSign v (seedUnitSource u k)) =
      (seedUnitRelativeNegative u v ^^ seedUnitSign (seedUnitRelativeIndex u v) k) := by
  decide +kernel +revert

theorem seedUnit_relative (u v : Fin 8) (w : SeedCoordinate → R) :
    (seedUnitOperator u).symm (seedUnitOperator v w) =
      if seedUnitRelativeNegative u v then -seedUnitOperator (seedUnitRelativeIndex u v) w
      else seedUnitOperator (seedUnitRelativeIndex u v) w := by
  funext z
  rcases z with ⟨r,k⟩
  simp only [ite_apply,Pi.neg_apply]
  change (seedUnitOperator u).symm (seedUnitOperator v w) (r,k)=
    signedBit (seedUnitRelativeNegative u v) (seedUnitOperator (seedUnitRelativeIndex u v) w (r,k))
  rw [seedUnit_inverse_action,seedUnit_action,seedUnit_action,signedBit_comp,signedBit_comp,
    (seedUnit_relative_data u v k).1,(seedUnit_relative_data u v k).2]


theorem seedUnit_pairing (u : Fin 8) (v w : SeedCoordinate → R) :
    seedPairing (seedUnitOperator u v) (seedUnitOperator u w)=seedPairing v w := by
  have hI (v w : SeedCoordinate → R) : seedPairing (seedIOperator v) (seedIOperator w)=seedPairing v w :=
    signedCoordinateOperator_pairing _ _ _ _
  have hR (v w : SeedCoordinate → R) : seedPairing (seedRhoOperator v) (seedRhoOperator w)=seedPairing v w :=
    signedCoordinateOperator_pairing _ _ _ _
  have hS (v w : SeedCoordinate → R) : seedPairing (seedSigmaOperator v) (seedSigmaOperator w)=seedPairing v w :=
    signedCoordinateOperator_pairing _ _ _ _
  fin_cases u <;> simp [seedUnitOperator,LinearEquiv.mul_apply,hI,hR,hS]


end Atlas.Rudvalis
