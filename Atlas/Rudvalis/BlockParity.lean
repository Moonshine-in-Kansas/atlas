import Atlas.Rudvalis.QuaternarySelfDual
import Atlas.Rudvalis.TorsionMinimum
import Atlas.Codes.QuaternaryWeight

/-! The literal block lift and the inactive-row parity obstruction of Version 33. -/
namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

def blockLiftSeedIndex (r t : Fin 7) : SeedOrbitIndex :=
  (r+t,(if t=2 then 1 else 0),(if t=0 ∨ t=1 then 1 else 0),0)

noncomputable def quaternaryBlockLift (r : Fin 7) : QuaternaryWord :=
  ∑ t : Fin 7, quaternarySeed (blockLiftSeedIndex r t)

theorem quaternaryBlockLift_mem (r : Fin 7) : quaternaryBlockLift r∈quaternaryCode :=
  Submodule.sum_mem _ (fun _ _ => quaternaryCode_seed _)

def blockLiftTable (r : Fin 7) (k : Fin 8) : ZMod 4 :=
  (![![1,1,1,1,1,1,1,1],![2,2,2,0,0,2,2,0],![0,0,0,2,0,2,0,2],
    ![2,0,0,2,0,0,2,0],![2,0,0,2,0,0,2,0],![0,0,0,2,2,0,2,0],
    ![0,2,2,2,2,2,0,0]] r k)

theorem quaternarySeed_coordinates (t : SeedOrbitIndex) (r : Fin 7) (k : Fin 8) :
    quaternarySeed t (seedCoordinateEquiv (r,k)) =
      ((signedPositionSign k * signedBit (seedUnitSign (seedPackedUnit t.2.1 t.2.2.1)
        (signedPositionIndex k)) (seedBaseArray t.2.2.2
          (seedShiftedRow t.1 r,seedUnitSource (seedPackedUnit t.2.1 t.2.2.1)
            (signedPositionIndex k))) : ℤ) : ZMod 4) := by
  unfold quaternarySeed seedOrbitWord
  rw [signedSeedTransport_apply]
  unfold seedOrbitOriginal
  rw [seedP_pow_apply,seedUnit_packed,seedUnit_action]
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem quaternaryBlockLift_coordinates (r s : Fin 7) (k : Fin 8) :
    quaternaryBlockLift r (seedCoordinateEquiv (s,k))=blockLiftTable (seedShiftedRow r s) k := by
  simp only [quaternaryBlockLift,Finset.sum_apply,quaternarySeed_coordinates]
  decide +kernel +revert

theorem quaternaryBlockLift_residue (r : Fin 7) :
    reduce (quaternaryBlockLift r)=rowWord (rowLabel r) := by
  funext z
  obtain ⟨⟨s,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  change reduceScalar (quaternaryBlockLift r (seedCoordinateEquiv (s,k)))=_
  rw [quaternaryBlockLift_coordinates]
  change reduceScalar (blockLiftTable (seedShiftedRow r s) k)=
    rowWord (rowLabel r) (rowLabel s,seedInnerLabel s k)
  decide +kernel +revert

def quaternaryRowSum (w : QuaternaryWord) (p : Point) : ZMod 4 := ∑ x : E,w (p,x)

theorem quaternaryBlockLift_inactive_sum (r s : Fin 7) (hrs : s≠r) :
    quaternaryRowSum (quaternaryBlockLift r) (rowLabel s)=2 := by
  unfold quaternaryRowSum
  rw [← Equiv.sum_comp (seedInnerEquiv s)]
  change (∑ k : Fin 8,quaternaryBlockLift r (seedCoordinateEquiv (s,k)))=2
  simp_rw [quaternaryBlockLift_coordinates]
  decide +kernel +revert

theorem double_torsion_row_sum (b : BinaryWord) (hb : b∈binaryTorsion) (p : Point) :
    quaternaryRowSum (double b) p=0 := by
  have he := (Atlas.Codes.even_weight_iff _).mp (binaryTorsion_row_even b hb p)
  change (∑ x : E,doubleScalar (b (p,x)))=0
  rw [← map_sum,he,map_zero]


theorem quaternary_inactive_row_sum (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (p q : Point) (hr : reduce w=rowWord p) (hqp : q≠p) : quaternaryRowSum w q=2 := by
  obtain ⟨r,rfl⟩ := rowLabel_bijective.2 p
  obtain ⟨s,rfl⟩ := rowLabel_bijective.2 q
  have hrs : s≠r := by intro h; subst s; exact hqp rfl
  have hzero : reduce (w-quaternaryBlockLift r)=0 := by
    rw [map_sub,hr,quaternaryBlockLift_residue,sub_self]
  obtain ⟨b,hb⟩ := (reduce_eq_zero _).mp hzero
  have hbt : b∈binaryTorsion := (quaternaryCode_torsion b).mp
    (hb.symm ▸ quaternaryCode.sub_mem hw (quaternaryBlockLift_mem r))
  have he := congrArg (fun v => quaternaryRowSum v (rowLabel s)) hb
  rw [double_torsion_row_sum b hbt] at he
  have hs : quaternaryRowSum (w-quaternaryBlockLift r) (rowLabel s)=
      quaternaryRowSum w (rowLabel s)-quaternaryRowSum (quaternaryBlockLift r) (rowLabel s) := by
    simp [quaternaryRowSum,Finset.sum_sub_distrib]
  rw [hs,quaternaryBlockLift_inactive_sum r s hrs] at he
  exact sub_eq_zero.mp he.symm

theorem quaternary_inactive_row_two (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (p q : Point) (hr : reduce w=rowWord p) (hqp : q≠p) : ∃ x : E,w (q,x)=2 := by
  have hsum := quaternary_inactive_row_sum w hw p q hr hqp
  have hzero (x : E) : reduceScalar (w (q,x))=0 := by
    have he := congrFun hr (q,x)
    simpa [reduce,rowWord,hqp] using he
  have heven : ∀ a : ZMod 4,reduceScalar a=0 → a=0 ∨ a=2 := by decide +kernel
  by_contra hn
  push_neg at hn
  have hz (x : E) : w (q,x)=0 := (heven _ (hzero x)).resolve_right (hn x)
  simp only [quaternaryRowSum,hz,Finset.sum_const_zero] at hsum
  exact (by decide : (0 : ZMod 4)≠2) hsum

theorem quaternary_active_row_weight (w : QuaternaryWord) (p : Point)
    (hr : reduce w=rowWord p) : (∑ x : E,euclideanSymbolWeight (w (p,x)))=8 := by
  have hodd : ∀ a : ZMod 4,reduceScalar a=1 → euclideanSymbolWeight a=1 := by decide +kernel
  have he (x : E) : euclideanSymbolWeight (w (p,x))=1 := by
    apply hodd
    have hx := congrFun hr (p,x)
    simpa [reduce,rowWord] using hx
  simp [he]

theorem quaternary_row_lift_lower (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (p : Point) (hr : reduce w=rowWord p) : 32 ≤ euclideanWeight w := by
  have hq (q : Point) : (if q=p then 8 else 4 : ℕ) ≤
      ∑ x : E,euclideanSymbolWeight (w (q,x)) := by
    by_cases hqp : q=p
    · subst q
      rw [if_pos rfl,quaternary_active_row_weight w p hr]
    · rw [if_neg hqp]
      obtain ⟨x,hx⟩ := quaternary_inactive_row_two w hw p q hr hqp
      have he := Finset.single_le_sum (fun (y : E) (_ : y∈Finset.univ) =>
        Nat.zero_le (euclideanSymbolWeight (w (q,y)))) (Finset.mem_univ x)
      rw [hx] at he
      exact he
  have he : (∑ q : Point,if q=p then (8 : ℕ) else 4)=32 := by
    have he0 : ∀ p : Point,(∑ q : Point,if q=p then (8 : ℕ) else 4)=32 := by decide +kernel
    exact he0 p
  rw [← he]
  change _ ≤ ∑ z : Coordinate,euclideanSymbolWeight (w z)
  rw [Fintype.sum_prod_type]
  exact Finset.sum_le_sum (fun q _ => hq q)

end Atlas.Rudvalis

