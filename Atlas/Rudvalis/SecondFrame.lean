import Atlas.Rudvalis.LatticeMonomial
import Atlas.Rudvalis.SeedCorrelations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The labeled Version33 second real frame P^{-r}(-Ib,b,-Iρb,ρb,-Iσb,σb,-IJ₃b,J₃b). -/
namespace Atlas.Rudvalis
open scoped BigOperators

set_option maxHeartbeats 2000000 in
theorem seedBB_correlation (d : Fin 7) (u : Fin 8) :
    seedCorrelation d u 1 1=if d=0 ∧ u=0 then 16 else 0 := by
  rw [seedCorrelation_eval]
  decide +kernel +revert

theorem seedB_translated_pairing (r s : Fin 7) (u v : Fin 8) :
    seedPairing ((seedPOperator^r.val) (seedUnitOperator u seedBArray))
      ((seedPOperator^s.val) (seedUnitOperator v seedBArray))=
      if r=s ∧ u=v then 16 else 0 := by
  have hP := operator_pow_pairing seedPOperator seedP_pairing r.val
    (seedUnitOperator u seedBArray)
    ((seedPOperator^r.val).symm ((seedPOperator^s.val) (seedUnitOperator v seedBArray)))
  rw [LinearEquiv.apply_symm_apply] at hP
  rw [hP,seedP_relative,seedP_unit_comm_power]
  have hU := seedUnit_pairing u seedBArray
    ((seedUnitOperator u).symm (seedUnitOperator v
      ((seedPOperator^(seedRelativeShift r s).val) seedBArray)))
  rw [LinearEquiv.apply_symm_apply] at hU
  rw [hU,seedUnit_relative]
  have hbase := seedBB_correlation (seedRelativeShift r s) (seedUnitRelativeIndex u v)
  change seedPairing seedBArray ((seedPOperator^(seedRelativeShift r s).val)
    (seedUnitOperator (seedUnitRelativeIndex u v) seedBArray))=_ at hbase
  rw [seedP_unit_comm_power] at hbase
  have he : (if seedUnitRelativeNegative u v then
      -(if seedRelativeShift r s=0 ∧ seedUnitRelativeIndex u v=0 then (16 : ℤ) else 0)
      else (if seedRelativeShift r s=0 ∧ seedUnitRelativeIndex u v=0 then 16 else 0))=
      (if r=s ∧ u=v then 16 else 0) := by
    clear hP hU hbase
    decide +kernel +revert
  by_cases hn : seedUnitRelativeNegative u v=true
  · rw [if_pos hn]
    simp only [seedPairing,Pi.neg_apply,mul_neg,Finset.sum_neg_distrib]
    change -seedPairing seedBArray (seedUnitOperator (seedUnitRelativeIndex u v)
      ((seedPOperator^(seedRelativeShift r s).val) seedBArray))=_
    rw [hbase]
    simpa [hn] using he
  · rw [if_neg hn,hbase]
    simpa [hn] using he

def secondFrameRow (r : Fin 7) : Fin 7 := ⟨(7-r.val)%7,Nat.mod_lt _ (by decide)⟩
def secondFrameUnit (k : Fin 8) : Fin 8 := ![4,0,5,1,6,2,7,3] k

def secondFrameOrbitIndex (z : SeedCoordinate) : SeedOrbitIndex :=
  (secondFrameRow z.1,(seedUnpackUnit (secondFrameUnit z.2)).1,
    (seedUnpackUnit (secondFrameUnit z.2)).2,1)

def secondFrameSign (k : Fin 8) : ℤ := if k.val%2=0 then -1 else 1

noncomputable def secondFrameInteger (z : SeedCoordinate) : IntegerCoordinates :=
  secondFrameSign z.2 • seedOrbitWord (secondFrameOrbitIndex z)

noncomputable def secondFrame (z : SeedCoordinate) : RationalSpace := halfCoordinates (secondFrameInteger z)

theorem secondFrameInteger_mem (z : SeedCoordinate) : secondFrameInteger z∈doubledLattice := by
  change reduceModFour (secondFrameSign z.2 • seedOrbitWord (secondFrameOrbitIndex z))∈quaternaryCode
  rw [map_smul]
  exact (quaternaryCode.restrictScalars ℤ).smul_mem _ (quaternaryCode_seed _)

theorem secondFrame_mem (z : SeedCoordinate) : secondFrame z∈rudvalisLattice :=
  Submodule.mem_map_of_mem (secondFrameInteger_mem z)

theorem secondFrameInteger_pairing (z w : SeedCoordinate) :
    integerDot (secondFrameInteger z) (secondFrameInteger w)=if z=w then 16 else 0 := by
  have he : (secondFrameSign z.2*secondFrameSign w.2)*
      (if secondFrameRow z.1=secondFrameRow w.1 ∧ secondFrameUnit z.2=secondFrameUnit w.2
        then (16 : ℤ) else 0)=(if z=w then 16 else 0) := by decide +kernel +revert
  have hb : integerDot (seedOrbitWord (secondFrameOrbitIndex z))
      (seedOrbitWord (secondFrameOrbitIndex w))=
      if secondFrameRow z.1=secondFrameRow w.1 ∧ secondFrameUnit z.2=secondFrameUnit w.2
        then 16 else 0 := by
    rw [integerDot,seedOrbitWord,seedOrbitWord,signedSeedTransport_pairing]
    unfold seedOrbitOriginal
    rw [seedUnit_packed,seedUnit_packed]
    simp only [secondFrameOrbitIndex,seedPacked_unpack,ite_false,show (1 : Fin 2)≠0 by decide]
    exact seedB_translated_pairing _ _ _ _
  calc
    _=(secondFrameSign z.2*secondFrameSign w.2)*
        integerDot (seedOrbitWord (secondFrameOrbitIndex z)) (seedOrbitWord (secondFrameOrbitIndex w)) := by
      simp only [integerDot,secondFrameInteger,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=_ := by rw [hb]; exact he

theorem secondFrame_pairing (z w : SeedCoordinate) :
    rationalDot (secondFrame z) (secondFrame w)=if z=w then 4 else 0 := by
  rw [secondFrame,secondFrame,rationalDot_half,secondFrameInteger_pairing]
  split_ifs <;> norm_num

end Atlas.Rudvalis
