import Atlas.Rudvalis.SeedOperatorProducts

namespace Atlas.Rudvalis
open scoped BigOperators
variable {R : Type*} [CommRing R]

def seedBaseArray (x : Fin 2) : SeedCoordinate → ℤ := if x=0 then seedAArray else seedBArray

noncomputable def seedCorrelation (d : Fin 7) (u : Fin 8) (x y : Fin 2) : ℤ :=
  seedPairing (seedBaseArray x) ((seedPOperator^d.val) (seedUnitOperator u (seedBaseArray y)))


def seedShiftedRow (d r : Fin 7) : Fin 7 := ⟨(r.val+7-d.val)%7,Nat.mod_lt _ (by decide)⟩

theorem seedP_pow_apply (d r : Fin 7) (k : Fin 8) (w : SeedCoordinate → R) :
    (seedPOperator^d.val) w (r,k)=w (seedShiftedRow d r,k) := by
  fin_cases d <;> fin_cases r <;> rfl

theorem seedCorrelation_eval (d : Fin 7) (u : Fin 8) (x y : Fin 2) :
    seedCorrelation d u x y = ∑ z : SeedCoordinate,
      seedBaseArray x z * signedBit (seedUnitSign u z.2)
        (seedBaseArray y (seedShiftedRow d z.1,seedUnitSource u z.2)) := by
  unfold seedCorrelation seedPairing
  apply Finset.sum_congr rfl
  rintro ⟨r,k⟩ _
  rw [seedP_pow_apply,seedUnit_action]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem seedCorrelation_divisible (d : Fin 7) (u : Fin 8) (x y : Fin 2) :
    4 ∣ seedCorrelation d u x y := by
  rw [seedCorrelation_eval]
  decide +kernel +revert



theorem seedP_pairing (v w : SeedCoordinate → R) :
    seedPairing (seedPOperator v) (seedPOperator w)=seedPairing v w :=
  signedCoordinateOperator_pairing _ _ _ _

theorem operator_pow_pairing (L : (SeedCoordinate → R) ≃ₗ[R] (SeedCoordinate → R))
    (hL : ∀ v w, seedPairing (L v) (L w)=seedPairing v w)
    (n : ℕ) (v w : SeedCoordinate → R) :
    seedPairing ((L^n) v) ((L^n) w)=seedPairing v w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change seedPairing (L ((L^n) v)) (L ((L^n) w))=_
    rw [hL,ih]

theorem seedP_unit_comm (u : Fin 8) (v : SeedCoordinate → R) :
    seedPOperator (seedUnitOperator u v)=seedUnitOperator u (seedPOperator v) := by
  funext z
  rcases z with ⟨r,k⟩
  change seedUnitOperator u v (seedRowCycle r,k)=seedUnitOperator u (seedPOperator v) (r,k)
  rw [seedUnit_action,seedUnit_action]
  rfl

theorem seedP_unit_comm_power (n : ℕ) (u : Fin 8) (v : SeedCoordinate → R) :
    (seedPOperator^n) (seedUnitOperator u v)=seedUnitOperator u ((seedPOperator^n) v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change seedPOperator ((seedPOperator^n) (seedUnitOperator u v))=
      seedUnitOperator u (seedPOperator ((seedPOperator^n) v))
    rw [ih,seedP_unit_comm]

def seedRelativeShift (r s : Fin 7) : Fin 7 := ⟨(s.val+7-r.val)%7,Nat.mod_lt _ (by decide)⟩

set_option maxHeartbeats 2000000 in
theorem seedP_relative (r s : Fin 7) (v : SeedCoordinate → R) :
    (seedPOperator^r.val).symm ((seedPOperator^s.val) v) =
      (seedPOperator^(seedRelativeShift r s).val) v := by
  fin_cases r <;> fin_cases s <;> funext z <;> rcases z with ⟨q,k⟩ <;> fin_cases q <;> rfl


theorem seedTranslated_pair_divisible (r s : Fin 7) (u v : Fin 8) (x y : Fin 2) :
    4 ∣ seedPairing ((seedPOperator^r.val) (seedUnitOperator u (seedBaseArray x)))
      ((seedPOperator^s.val) (seedUnitOperator v (seedBaseArray y))) := by
  have hP := operator_pow_pairing seedPOperator seedP_pairing r.val
    (seedUnitOperator u (seedBaseArray x))
    ((seedPOperator^r.val).symm ((seedPOperator^s.val) (seedUnitOperator v (seedBaseArray y))))
  rw [LinearEquiv.apply_symm_apply] at hP
  rw [hP,seedP_relative,seedP_unit_comm_power]
  have hU := seedUnit_pairing u (seedBaseArray x)
    ((seedUnitOperator u).symm (seedUnitOperator v
      ((seedPOperator^(seedRelativeShift r s).val) (seedBaseArray y))))
  rw [LinearEquiv.apply_symm_apply] at hU
  rw [hU,seedUnit_relative]
  have hbase := seedCorrelation_divisible (seedRelativeShift r s) (seedUnitRelativeIndex u v) x y
  unfold seedCorrelation at hbase
  rw [seedP_unit_comm_power] at hbase
  split_ifs
  · simpa [seedPairing,Finset.sum_neg_distrib] using (dvd_neg.mpr hbase)
  · exact hbase

def seedPackedUnit (e : Fin 2) (s : Fin 4) : Fin 8 := ⟨4*e.val+s.val,by omega⟩

theorem seedUnit_packed (e : Fin 2) (s : Fin 4) (v : SeedCoordinate → R) :
    (seedIOperator^e.val) (seedJOperator s v)=seedUnitOperator (seedPackedUnit e s) v := by
  fin_cases e <;> fin_cases s <;> rfl

theorem seedOrbitOriginal_pair_divisible (a b : SeedOrbitIndex) :
    4 ∣ seedPairing (seedOrbitOriginal a) (seedOrbitOriginal b) := by
  unfold seedOrbitOriginal
  rw [seedUnit_packed,seedUnit_packed]
  exact seedTranslated_pair_divisible _ _ _ _ _ _

theorem signedSeedTransport_pairing (v w : SeedCoordinate → ℤ) :
    (∑ z : Coordinate,signedSeedTransport v z*signedSeedTransport w z)=seedPairing v w := by
  rw [← Equiv.sum_comp seedCoordinateEquiv]
  have he (z : SeedCoordinate) : signedSeedTransport v (seedCoordinateEquiv z)*
      signedSeedTransport w (seedCoordinateEquiv z)=
      v (z.1,signedPositionIndex z.2)*w (z.1,signedPositionIndex z.2) := by
    rw [show z=(z.1,z.2) from rfl,signedSeedTransport_apply,signedSeedTransport_apply]
    by_cases hz : z.2=1 <;> simp [signedPositionSign,hz]
  simp_rw [he]
  exact Equiv.sum_comp (Equiv.prodCongr (Equiv.refl _) signedPositionIndexEquiv)
    (fun z=>v z*w z)

theorem seedOrbitWord_pair_divisible (a b : SeedOrbitIndex) :
    4 ∣ ∑ z : Coordinate,seedOrbitWord a z*seedOrbitWord b z := by
  rw [seedOrbitWord,seedOrbitWord,signedSeedTransport_pairing]
  exact seedOrbitOriginal_pair_divisible a b

end Atlas.Rudvalis

