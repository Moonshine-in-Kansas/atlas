import Atlas.Rudvalis.SeedCorrelations

/-! Closure of the literal defining seed orbit under its signed operators. -/
namespace Atlas.Rudvalis
variable {R : Type*} [CommRing R]

def seedUnitProductIndex (u v : Fin 8) : Fin 8 := seedUnitRelativeIndex u v

def seedUnitProductNegative (u v : Fin 8) : Bool :=
  seedUnitSign u 0 ^^ seedUnitSign v (seedUnitSource u 0) ^^
    seedUnitSign (seedUnitProductIndex u v) 0

theorem seedUnit_product_data (u v k : Fin 8) :
    seedUnitSource v (seedUnitSource u k)=seedUnitSource (seedUnitProductIndex u v) k ∧
    (seedUnitSign u k ^^ seedUnitSign v (seedUnitSource u k)) =
      (seedUnitProductNegative u v ^^ seedUnitSign (seedUnitProductIndex u v) k) := by
  decide +kernel +revert

theorem seedUnit_product (u v : Fin 8) (w : SeedCoordinate → R) :
    seedUnitOperator u (seedUnitOperator v w)=
      if seedUnitProductNegative u v then -seedUnitOperator (seedUnitProductIndex u v) w
      else seedUnitOperator (seedUnitProductIndex u v) w := by
  funext z
  rcases z with ⟨r,k⟩
  simp only [ite_apply,Pi.neg_apply]
  change seedUnitOperator u (seedUnitOperator v w) (r,k)=
    signedBit (seedUnitProductNegative u v) (seedUnitOperator (seedUnitProductIndex u v) w (r,k))
  rw [seedUnit_action,seedUnit_action,seedUnit_action,signedBit_comp,signedBit_comp,
    (seedUnit_product_data u v k).1,(seedUnit_product_data u v k).2]

def seedNextRow (r : Fin 7) : Fin 7 := ⟨(r.val+1)%7,Nat.mod_lt _ (by decide)⟩

theorem seedP_next (r : Fin 7) (w : SeedCoordinate → R) :
    seedPOperator ((seedPOperator^r.val) w)=(seedPOperator^(seedNextRow r).val) w := by
  funext z
  rcases z with ⟨a,k⟩
  change (seedPOperator^r.val) w (seedRowCycle a,k)=_
  rw [seedP_pow_apply,seedP_pow_apply]
  congr 1
  decide +kernel +revert

def seedUnpackUnit (u : Fin 8) : Fin 2 × Fin 4 :=
  (⟨u.val/4,by omega⟩,⟨u.val%4,Nat.mod_lt _ (by decide)⟩)

theorem seedPacked_unpack (u : Fin 8) :
    seedPackedUnit (seedUnpackUnit u).1 (seedUnpackUnit u).2=u := by
  decide +kernel +revert

def seedUnitOrbitIndex (u : Fin 8) (t : SeedOrbitIndex) : SeedOrbitIndex :=
  let v := seedUnpackUnit (seedUnitProductIndex u (seedPackedUnit t.2.1 t.2.2.1))
  (t.1,v.1,v.2,t.2.2.2)

theorem seedOrbitOriginal_unit (u : Fin 8) (t : SeedOrbitIndex) :
    seedUnitOperator u (seedOrbitOriginal t)=
      if seedUnitProductNegative u (seedPackedUnit t.2.1 t.2.2.1)
      then -seedOrbitOriginal (seedUnitOrbitIndex u t)
      else seedOrbitOriginal (seedUnitOrbitIndex u t) := by
  unfold seedOrbitOriginal
  rw [seedUnit_packed,← seedP_unit_comm_power,seedUnit_product]
  simp only [seedUnitOrbitIndex,seedUnit_packed,seedPacked_unpack]
  split <;> simp_all <;> rfl

theorem seedOrbitOriginal_P (t : SeedOrbitIndex) :
    seedPOperator (seedOrbitOriginal t)=
      seedOrbitOriginal (seedNextRow t.1,t.2) := by
  exact seedP_next t.1 _

end Atlas.Rudvalis
