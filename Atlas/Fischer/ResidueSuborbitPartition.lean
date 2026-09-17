import Atlas.Fischer.ResidueQuotientGeometry
import Atlas.Fischer.ResidueKernelCocode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The literal fixed, commuting, and noncommuting classes on original points. -/
def residueSuborbitIndex (S : Finset Omega) (i : Omega) (hi : i ∉ S)
    (x : ResiduePoint S) : Fin 3 :=
  if x=residueBasicPoint S i hi then 0 else
    if Commute (distinguishedRootElement (.inl i)) x.val then 1 else 2

theorem residueSuborbitIndex_zero_iff (S : Finset Omega) (i : Omega) (hi : i ∉ S)
    (x : ResiduePoint S) :
    residueSuborbitIndex S i hi x=0 ↔ x=residueBasicPoint S i hi := by
  simp only [residueSuborbitIndex]
  split_ifs <;> simp_all

theorem residueSuborbitIndex_one_iff (S : Finset Omega) (i : Omega) (hi : i ∉ S)
    (x : ResiduePoint S) :
    residueSuborbitIndex S i hi x=1 ↔
      x ≠ residueBasicPoint S i hi ∧ Commute (distinguishedRootElement (.inl i)) x.val := by
  simp only [residueSuborbitIndex]
  split_ifs <;> simp_all

theorem residueSuborbitIndex_two_iff (S : Finset Omega) (i : Omega) (hi : i ∉ S)
    (x : ResiduePoint S) :
    residueSuborbitIndex S i hi x=2 ↔
      ¬Commute (distinguishedRootElement (.inl i)) x.val := by
  have hc : Commute (distinguishedRootElement (.inl i))
      (residueBasicPoint S i hi).val := Commute.refl _
  simp only [residueSuborbitIndex]
  split_ifs <;> simp_all

theorem residueSuborbitIndex_base (S : Finset Omega) (i : Omega) (hi : i ∉ S) :
    residueSuborbitIndex S i hi (residueBasicPoint S i hi)=0 := by
  exact (residueSuborbitIndex_zero_iff S i hi _).mpr rfl

/-- The commuting class is exactly the next original residue, before quotienting. -/
def residueCommutingFiberEquiv (S : Finset Omega) (i : Omega) (hi : i ∉ S) :
    {x : ResiduePoint S // residueSuborbitIndex S i hi x=1} ≃ ResiduePoint (insert i S) where
  toFun x := ⟨x.val.val,x.val.property.1,by
    rintro ⟨j,hj,hjv⟩
    rcases Finset.mem_insert.mp hj with hj | hj
    · subst j
      exact ((residueSuborbitIndex_one_iff S i hi x.val).mp x.property).1
        (Subtype.ext hjv.symm)
    · exact x.val.property.2.1 ⟨j,hj,hjv⟩,
    by
      intro j hj
      rcases Finset.mem_insert.mp hj with hj | hj
      · subst j
        exact ((residueSuborbitIndex_one_iff S i hi x.val).mp x.property).2
      · exact x.val.property.2.2 j hj⟩
  invFun x :=
    let y : ResiduePoint S := ⟨x.val,x.property.1,
      fun ⟨j,hj,hjv⟩ => x.property.2.1 ⟨j,Finset.mem_insert_of_mem hj,hjv⟩,
      fun j hj => x.property.2.2 j (Finset.mem_insert_of_mem hj)⟩
    ⟨y,(residueSuborbitIndex_one_iff S i hi y).mpr ⟨by
      intro he
      exact x.property.2.1 ⟨i,Finset.mem_insert_self _ _,(congrArg Subtype.val he).symm⟩,
      x.property.2.2 i (Finset.mem_insert_self _ _)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Atlas.Fischer
