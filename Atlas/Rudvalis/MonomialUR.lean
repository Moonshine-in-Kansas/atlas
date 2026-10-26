import Atlas.Rudvalis.QuaternaryPresentation

/-! The literal U and R complex-monomial tables, in original real coordinates.
The real arrays expand z=(e₁,e₂,e₄,e₆), iz=(-e₀,e₃,e₅,e₇).
Both table permutations are involutions, so source images also describe inverse indexing. -/
namespace Atlas.Rudvalis
def seedUInner (r : Fin 7) (k : Fin 8) : Fin 8 :=
  ![![0,1,2,3,4,5,6,7],![7,6,5,4,3,2,1,0],![3,2,1,0,7,6,5,4],![2,3,0,1,6,7,4,5],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![4,5,6,7,0,1,2,3]] r k
def seedUSign (r : Fin 7) (k : Fin 8) : Bool :=
  ![![true,true,true,true,true,true,true,true],![true,false,false,true,true,false,false,true],![true,false,false,true,true,false,false,true],![false,false,false,false,false,false,false,false],![true,true,false,false,true,true,false,false],![false,false,true,true,true,true,false,false],![true,true,false,false,true,true,false,false]] r k
def seedRInner (r : Fin 7) (k : Fin 8) : Fin 8 :=
  ![![0,1,2,3,6,7,4,5],![0,1,5,4,7,6,2,3],![0,1,6,7,3,2,5,4],![1,0,5,4,2,3,6,7],![5,4,6,7,1,0,2,3],![7,6,2,3,4,5,1,0],![1,0,4,5,3,2,6,7]] r k
def seedRSign (r : Fin 7) (k : Fin 8) : Bool :=
  ![![false,false,false,false,false,false,false,false],![false,false,false,true,true,false,false,false],![false,false,false,false,true,false,false,true],![false,true,true,false,false,false,false,false],![true,false,true,true,false,true,true,true],![false,true,false,false,false,false,true,false],![true,false,false,false,false,true,false,false]] r k

def seedRRow (r : Fin 7) : Fin 7 := ![0,2,1,6,4,5,3] r

def seedUCoord : Equiv.Perm SeedCoordinate :=
  ⟨fun z => (z.1,seedUInner z.1 z.2),fun z => (z.1,seedUInner z.1 z.2),
    by decide +kernel,by decide +kernel⟩
def seedRCoord : Equiv.Perm SeedCoordinate :=
  ⟨fun z => (seedRRow z.1,seedRInner z.1 z.2),
    fun z => (seedRRow z.1,seedRInner z.1 z.2),by decide +kernel,by decide +kernel⟩

theorem seedUSign_invariant (z : SeedCoordinate) :
    seedUSign (seedUCoord z).1 (seedUCoord z).2=seedUSign z.1 z.2 := by decide +kernel +revert

theorem seedRSign_invariant (z : SeedCoordinate) :
    seedRSign (seedRCoord z).1 (seedRCoord z).2=seedRSign z.1 z.2 := by decide +kernel +revert

noncomputable def seedUOperator {R : Type*} [CommRing R] :
    (SeedCoordinate→R) ≃ₗ[R] (SeedCoordinate→R) :=
  signedCoordinateOperator seedUCoord (fun z => seedUSign z.1 z.2)
noncomputable def seedROperator {R : Type*} [CommRing R] :
    (SeedCoordinate→R) ≃ₗ[R] (SeedCoordinate→R) :=
  signedCoordinateOperator seedRCoord (fun z => seedRSign z.1 z.2)

variable {R : Type*} [CommRing R]

theorem seedU_square (v : SeedCoordinate→R) : seedUOperator (seedUOperator v)=v := by
  funext z
  change (if seedUSign z.1 z.2 then -(if seedUSign (seedUCoord z).1 (seedUCoord z).2
    then -v (seedUCoord (seedUCoord z)) else v (seedUCoord (seedUCoord z)))
    else (if seedUSign (seedUCoord z).1 (seedUCoord z).2
    then -v (seedUCoord (seedUCoord z)) else v (seedUCoord (seedUCoord z))))=v z
  have hz : seedUCoord (seedUCoord z)=z := seedUCoord.left_inv z
  rw [seedUSign_invariant,hz]
  split <;> simp_all

theorem seedR_square (v : SeedCoordinate→R) : seedROperator (seedROperator v)=v := by
  funext z
  change (if seedRSign z.1 z.2 then -(if seedRSign (seedRCoord z).1 (seedRCoord z).2
    then -v (seedRCoord (seedRCoord z)) else v (seedRCoord (seedRCoord z)))
    else (if seedRSign (seedRCoord z).1 (seedRCoord z).2
    then -v (seedRCoord (seedRCoord z)) else v (seedRCoord (seedRCoord z))))=v z
  have hz : seedRCoord (seedRCoord z)=z := seedRCoord.left_inv z
  rw [seedRSign_invariant,hz]
  split <;> simp_all

noncomputable def seedTransportLinear : (SeedCoordinate→R) ≃ₗ[R] (Coordinate→R) :=
  (signedCoordinateOperator (Equiv.prodCongr (Equiv.refl _) signedPositionIndexEquiv)
    (fun z => z.2==1)).trans (LinearEquiv.piCongrLeft' R (fun _ : SeedCoordinate => R) seedCoordinateEquiv)

theorem seedTransportLinear_apply (v : SeedCoordinate→R) (z : SeedCoordinate) :
    seedTransportLinear v (seedCoordinateEquiv z)=
      if z.2=1 then -v (z.1,signedPositionIndex z.2) else v (z.1,signedPositionIndex z.2) := by
  simp [seedTransportLinear,LinearEquiv.trans_apply,LinearEquiv.piCongrLeft',signedCoordinateOperator,
    signedPositionIndexEquiv,Prod.map_def]

noncomputable def rudvalisUOperator : (Coordinate→R) ≃ₗ[R] (Coordinate→R) :=
  seedTransportLinear.symm.trans (seedUOperator.trans seedTransportLinear)
noncomputable def rudvalisROperator : (Coordinate→R) ≃ₗ[R] (Coordinate→R) :=
  seedTransportLinear.symm.trans (seedROperator.trans seedTransportLinear)

theorem rudvalisU_square (v : Coordinate→R) : rudvalisUOperator (rudvalisUOperator v)=v := by
  simp only [rudvalisUOperator,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,seedU_square,
    LinearEquiv.apply_symm_apply]

theorem rudvalisR_square (v : Coordinate→R) : rudvalisROperator (rudvalisROperator v)=v := by
  simp only [rudvalisROperator,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,seedR_square,
    LinearEquiv.apply_symm_apply]

open scoped BigOperators

theorem seedTransportLinear_pairing (v w : SeedCoordinate→R) :
    (∑ z,seedTransportLinear v z * seedTransportLinear w z)=∑z,v z*w z := by
  rw [← Equiv.sum_comp seedCoordinateEquiv]
  simp_rw [seedTransportLinear_apply]
  have he (z : SeedCoordinate) :
      (if z.2=1 then -v (z.1,signedPositionIndex z.2) else v (z.1,signedPositionIndex z.2))*
      (if z.2=1 then -w (z.1,signedPositionIndex z.2) else w (z.1,signedPositionIndex z.2))=
      v (z.1,signedPositionIndex z.2)*w (z.1,signedPositionIndex z.2) := by split <;> simp
  simp_rw [he]
  exact Equiv.sum_comp (Equiv.prodCongr (Equiv.refl _) signedPositionIndexEquiv) (fun z=>v z*w z)

theorem seedTransportLinear_symm_pairing (v w : Coordinate→R) :
    (∑ z,seedTransportLinear.symm v z * seedTransportLinear.symm w z)=∑z,v z*w z := by
  have h := seedTransportLinear_pairing (seedTransportLinear.symm v) (seedTransportLinear.symm w)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

theorem rudvalisU_pairing (v w : Coordinate→R) :
    (∑ z,rudvalisUOperator v z * rudvalisUOperator w z)=∑z,v z*w z := by
  change (∑z, seedTransportLinear (seedUOperator (seedTransportLinear.symm v)) z *
    seedTransportLinear (seedUOperator (seedTransportLinear.symm w)) z)=_
  rw [seedTransportLinear_pairing]
  change (∑z,signedCoordinateOperator seedUCoord _ (seedTransportLinear.symm v) z *
    signedCoordinateOperator seedUCoord _ (seedTransportLinear.symm w) z)=_
  exact (signedCoordinateOperator_pairing seedUCoord (fun z=>seedUSign z.1 z.2)
    (seedTransportLinear.symm v) (seedTransportLinear.symm w)).trans
      (seedTransportLinear_symm_pairing v w)

theorem rudvalisR_pairing (v w : Coordinate→R) :
    (∑ z,rudvalisROperator v z * rudvalisROperator w z)=∑z,v z*w z := by
  change (∑z, seedTransportLinear (seedROperator (seedTransportLinear.symm v)) z *
    seedTransportLinear (seedROperator (seedTransportLinear.symm w)) z)=_
  rw [seedTransportLinear_pairing]
  change (∑z,signedCoordinateOperator seedRCoord _ (seedTransportLinear.symm v) z *
    signedCoordinateOperator seedRCoord _ (seedTransportLinear.symm w) z)=_
  exact (signedCoordinateOperator_pairing seedRCoord (fun z=>seedRSign z.1 z.2)
    (seedTransportLinear.symm v) (seedTransportLinear.symm w)).trans
      (seedTransportLinear_symm_pairing v w)

end Atlas.Rudvalis

