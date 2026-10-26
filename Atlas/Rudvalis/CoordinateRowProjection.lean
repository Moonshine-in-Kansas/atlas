import Atlas.Rudvalis.ReferenceConfigurations

namespace Atlas.Rudvalis
open scoped BigOperators
open Classical

noncomputable def coordinateRowProjection (s : Set Point) : RationalSpace →ₗ[ℚ] RationalSpace := by
  classical
  exact {
    toFun := fun v i => if i.1∈s then v i else 0
    map_add' := by intro v w; ext i; split_ifs <;> simp_all
    map_smul' := by intro a v; ext i; split_ifs <;> simp_all }

noncomputable def coordinateRowEnergy (s : Set Point) (v : RationalSpace) : ℚ :=
  rationalDot (coordinateRowProjection s v) (coordinateRowProjection s v)

theorem coordinateRowProjection_apply (s : Set Point) (v : RationalSpace) (i : Coordinate) :
    coordinateRowProjection s v i=if i.1∈s then v i else 0 := by
  rfl

theorem coordinateRowProjection_idempotent (s : Set Point) (v : RationalSpace) :
    coordinateRowProjection s (coordinateRowProjection s v)=coordinateRowProjection s v := by
  classical
  ext i
  simp only [coordinateRowProjection_apply]
  split_ifs <;> rfl

theorem coordinateRowProjection_selfadjoint (s : Set Point) (v w : RationalSpace) :
    rationalDot (coordinateRowProjection s v) w=rationalDot v (coordinateRowProjection s w) := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  change (if i.1∈s then v i else 0)*w i=v i*(if i.1∈s then w i else 0)
  split_ifs <;> simp

theorem coordinateRowEnergy_half (s : Set Point) (z : IntegerCoordinates) :
    coordinateRowEnergy s (halfCoordinates z)=
      (∑ i : Coordinate,if i.1∈s then (z i : ℚ)^2 else 0)/4 := by
  classical
  unfold coordinateRowEnergy rationalDot
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coordinateRowProjection_apply]
  change (if i.1∈s then (z i:ℚ)/2 else 0)*(if i.1∈s then (z i:ℚ)/2 else 0)=_
  split_ifs <;> ring

theorem coordinateRowProjection_complement (s : Set Point) (v : RationalSpace) :
    coordinateRowProjection s v+coordinateRowProjection sᶜ v=v := by
  classical
  ext i
  simp only [Pi.add_apply,coordinateRowProjection_apply,Set.mem_compl_iff]
  split_ifs <;> simp_all

theorem coordinateRowEnergy_complement (s : Set Point) (v : RationalSpace) :
    coordinateRowEnergy s v+coordinateRowEnergy sᶜ v=rationalDot v v := by
  classical
  unfold coordinateRowEnergy rationalDot
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coordinateRowProjection_apply,Set.mem_compl_iff]
  split_ifs <;> simp_all

theorem coordinateRowProjection_gaussian (s : Set Point) (v : RationalSpace) :
    coordinateRowProjection s (rationalI v)=rationalI (coordinateRowProjection s v) := by
  classical
  ext i
  have hr : (codeI.val.right.symm i).1=i.1 := by
    have he := congrArg Prod.fst (codeI.val.right.apply_symm_apply i)
    rw [codeI_coordinate] at he
    exact he
  change (if i.1∈s then liftedSign (codeI.val.left.toAdd i) (v (codeI.val.right.symm i)) else 0)=
    liftedSign (codeI.val.left.toAdd i) (if (codeI.val.right.symm i).1∈s then v (codeI.val.right.symm i) else 0)
  rw [hr]
  split_ifs <;> simp [liftedSign]

end Atlas.Rudvalis
