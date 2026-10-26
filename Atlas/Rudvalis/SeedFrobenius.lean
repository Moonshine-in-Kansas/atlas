import Atlas.Rudvalis.SeedFrobeniusPermutation
import Atlas.Rudvalis.SeedIntegralTransport

/-! The literal Frobenius permutation, proved to preserve the defining seed orbit. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
variable {R : Type*} [CommRing R]

noncomputable def seedTOperator : (SeedCoordinate→R) ≃ₗ[R] (SeedCoordinate→R) :=
  signedCoordinateOperator seedTCoord (fun _ => false)

def seedTUnit (u : Fin 8) : Fin 8 := ![0,2,3,1,4,6,7,5] u

def seedDoubleRow (r : Fin 7) : Fin 7 := ⟨(2*r.val)%7,Nat.mod_lt _ (by decide)⟩

theorem seedT_unit_data (u k : Fin 8) :
    seedUnitSource u (seedTIndex k)=seedTIndex (seedUnitSource (seedTUnit u) k) ∧
    seedUnitSign u (seedTIndex k)=seedUnitSign (seedTUnit u) k := by
  decide +kernel +revert

theorem seedT_unit (u : Fin 8) (v : SeedCoordinate→R) :
    seedTOperator (seedUnitOperator u v)=seedUnitOperator (seedTUnit u) (seedTOperator v) := by
  funext z
  rcases z with ⟨r,k⟩
  change seedUnitOperator u v (seedTRowEquiv r,seedTIndex k)=_
  rw [seedUnit_action,seedUnit_action]
  change signedBit (seedUnitSign u (seedTIndex k))
    (v (seedTRowEquiv r,seedUnitSource u (seedTIndex k)))=
    signedBit (seedUnitSign (seedTUnit u) k)
      (v (seedTRowEquiv r,seedTIndex (seedUnitSource (seedTUnit u) k)))
  rw [(seedT_unit_data u k).1,(seedT_unit_data u k).2]

theorem seedT_Ppow (r : Fin 7) (v : SeedCoordinate→R) :
    seedTOperator ((seedPOperator^r.val) v)=
      (seedPOperator^(seedDoubleRow r).val) (seedTOperator v) := by
  funext z
  rcases z with ⟨q,k⟩
  change (seedPOperator^r.val) v (seedTRowEquiv q,seedTIndex k)=_
  rw [seedP_pow_apply,seedP_pow_apply]
  change v (seedShiftedRow r (seedTRowEquiv q),seedTIndex k)=
    v (seedTRowEquiv (seedShiftedRow (seedDoubleRow r) q),seedTIndex k)
  congr 2
  decide +kernel +revert

theorem seedT_base (x : Fin 2) : seedTOperator (seedBaseArray x)=seedBaseArray x := by
  funext z
  change seedBaseArray x (seedTCoord z)=seedBaseArray x z
  decide +kernel +revert

def seedTOrbitIndex (t : SeedOrbitIndex) : SeedOrbitIndex :=
  let u := seedUnpackUnit (seedTUnit (seedPackedUnit t.2.1 t.2.2.1))
  (seedDoubleRow t.1,u.1,u.2,t.2.2.2)

theorem seedT_orbit (t : SeedOrbitIndex) :
    seedTOperator (seedOrbitOriginal t)=seedOrbitOriginal (seedTOrbitIndex t) := by
  unfold seedOrbitOriginal
  rw [seedUnit_packed,seedT_Ppow,seedT_unit]
  change (seedPOperator^(seedDoubleRow t.1).val)
    (seedUnitOperator (seedTUnit (seedPackedUnit t.2.1 t.2.2.1)) (seedTOperator (seedBaseArray t.2.2.2)))=_
  rw [seedT_base]
  simp only [seedTOrbitIndex,seedUnit_packed,seedPacked_unpack]
  rfl

noncomputable def seedTMonomial : SignedCoordinates SeedCoordinate where
  left := 1
  right := seedTCoord.symm

noncomputable def rudvalisTMonomial : SignedCoordinates Coordinate := seedConjugateMonomial seedTMonomial

theorem seedTMonomial_apply (v : SeedCoordinate→ZMod 4) :
    monomialHom seedTMonomial v=seedTOperator v := rfl

theorem seedT_cast (v : SeedCoordinate→ℤ) :
    seedTOperator (fun z => (v z : ZMod 4))=
      fun z => ((seedTOperator (R:=ℤ) v z : ℤ) : ZMod 4) := rfl

theorem rudvalisTMonomial_seed (t : SeedOrbitIndex) :
    monomialHom rudvalisTMonomial (quaternarySeed t)=quaternarySeed (seedTOrbitIndex t) := by
  rw [quaternarySeed_transport,rudvalisTMonomial,seedConjugateMonomial_transport,
    seedTMonomial_apply,seedT_cast,seedT_orbit,←quaternarySeed_transport]

noncomputable def codeT : codeGroup := ⟨rudvalisTMonomial,by
  apply monomial_mem_codeGroup_of_seeds
  intro t
  rw [rudvalisTMonomial_seed]
  exact quaternaryCode_seed _⟩

end Atlas.Rudvalis
