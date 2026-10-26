import Atlas.Rudvalis.BlockParity

/-! Intrinsic inactive-block parity functionals from the actual quaternary lift. -/
namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

def quaternaryRowIndicator (p : Point) : QuaternaryWord := fun z => if z.1=p then 1 else 0

noncomputable def blockLiftHalf (r : Fin 7) : BinaryWord := fun z =>
  if quaternaryBlockLift r z=2 then 1 else 0

theorem blockLift_decomposition (r : Fin 7) :
    quaternaryBlockLift r=quaternaryRowIndicator (rowLabel r)+double (blockLiftHalf r) := by
  funext z
  obtain ⟨⟨s,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  change quaternaryBlockLift r (seedCoordinateEquiv (s,k)) =
    (if rowLabel s=rowLabel r then 1 else 0)+
      doubleScalar (if quaternaryBlockLift r (seedCoordinateEquiv (s,k))=2 then 1 else 0)
  rw [quaternaryBlockLift_coordinates]
  decide +kernel +revert

noncomputable def blockParityFunctional (r : Fin 7) : BinaryWord →ₗ[Bit] Bit :=
  binaryForm (blockLiftHalf r)

theorem quaternaryRowIndicator_pairing (p : Point) (w : QuaternaryWord) :
    quaternaryForm (quaternaryRowIndicator p) w=quaternaryRowSum w p := by
  change (∑ z : Coordinate,(if z.1=p then (1 : ZMod 4) else 0)*w z)=_
  rw [Fintype.sum_prod_type]
  simp [quaternaryRowSum,ite_mul]

theorem blockParityFunctional_row_sum (r : Fin 7) (w : QuaternaryWord) (hw : w∈quaternaryCode) :
    quaternaryRowSum w (rowLabel r)=doubleScalar (blockParityFunctional r (reduce w)) := by
  have he := quaternaryCode_self_orthogonal hw (quaternaryBlockLift r) (quaternaryBlockLift_mem r)
  rw [blockLift_decomposition,map_add,LinearMap.add_apply,quaternaryRowIndicator_pairing,
    double_pairing] at he
  have hn : ∀ b : Bit,-doubleScalar b=doubleScalar b := by decide +kernel
  exact (eq_neg_of_add_eq_zero_left he).trans (hn _)

def rowTwoCount (w : QuaternaryWord) (p : Point) : ℕ :=
  (Finset.univ.filter (fun x : E => w (p,x)=2)).card

theorem inactive_row_double_count (w : QuaternaryWord) (p : Point)
    (hzero : ∀ x : E,reduce w (p,x)=0) :
    quaternaryRowSum w p=doubleScalar (rowTwoCount w p : Bit) := by
  have he : ∀ a : ZMod 4,reduceScalar a=0 → a=doubleScalar (if a=2 then 1 else 0) := by
    decide +kernel
  change (∑ x : E,w (p,x))=_
  calc
    (∑ x : E,w (p,x)) = ∑ x : E,doubleScalar (if w (p,x)=2 then 1 else 0) :=
      Finset.sum_congr rfl (fun x _ => he (w (p,x)) (hzero x))
    _ = _ := by
      rw [← map_sum]
      congr 1
      simp only [rowTwoCount,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem blockParityFunctional_inactive (r : Fin 7) (w : QuaternaryWord)
    (hw : w∈quaternaryCode) (hzero : ∀ x : E,reduce w (rowLabel r,x)=0) :
    (rowTwoCount w (rowLabel r) : Bit)=blockParityFunctional r (reduce w) := by
  apply doubleScalar_injective
  rw [← inactive_row_double_count w (rowLabel r) hzero,blockParityFunctional_row_sum r w hw]

theorem block_half_difference_torsion (p : Point) (h k : BinaryWord)
    (hh : quaternaryRowIndicator p+double h∈quaternaryCode)
    (hk : quaternaryRowIndicator p+double k∈quaternaryCode) : h-k∈binaryTorsion := by
  apply (quaternaryCode_torsion _).mp
  have he : double (h-k)=(quaternaryRowIndicator p+double h)-(quaternaryRowIndicator p+double k) := by
    rw [map_sub]
    abel
  rw [he]
  exact quaternaryCode.sub_mem hh hk

theorem blockParityFunctional_independent (r : Fin 7) (h : BinaryWord)
    (hh : quaternaryRowIndicator (rowLabel r)+double h∈quaternaryCode)
    (d : BinaryWord) (hd : d∈binaryResidue) : binaryForm h d=blockParityFunctional r d := by
  have hk : quaternaryRowIndicator (rowLabel r)+double (blockLiftHalf r)∈quaternaryCode := by
    rw [← blockLift_decomposition]
    exact quaternaryBlockLift_mem r
  have ht := block_half_difference_torsion (rowLabel r) h (blockLiftHalf r) hh hk
  have he : binaryForm (h-blockLiftHalf r) d=0 := by
    rw [binaryForm_symmetric]
    exact ht d hd
  rw [map_sub,LinearMap.sub_apply] at he
  exact sub_eq_zero.mp he

end Atlas.Rudvalis
