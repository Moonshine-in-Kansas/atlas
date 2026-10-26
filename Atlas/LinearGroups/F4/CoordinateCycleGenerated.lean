import Atlas.LinearGroups.F4.RootGeneratedElements

/-! The coordinate cycle is an actual word in the constructed short root groups.
The finite certificate checks only its signed action on the 27 integral basis vectors. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

def shortWeylPair (p : Fin 3) (i : Fin 8) : Model F :=
  shortRoot p i 1*shortRoot p (7-i) 1*shortRoot p i 1

theorem shortWeylPair_conjugate (p : Fin 3) (i : Fin 8) :
    shortWeylPair (F := F) p i=coordinateCycle^p.val*shortWeylFirstPair i*(coordinateCycle^p.val)⁻¹ := by
  unfold shortWeylPair shortRoot shortWeylFirstPair
  group

theorem shortWeylPair_mem_rootGenerated (p : Fin 3) (i : Fin 8) :
    shortWeylPair (F := F) p i∈rootGenerated :=
  (rootGenerated (F := F)).mul_mem
    ((rootGenerated (F := F)).mul_mem (shortRoot_mem_rootGenerated p i 1)
      (shortRoot_mem_rootGenerated p (7-i) 1))
    (shortRoot_mem_rootGenerated p i 1)

private theorem coordinateCycle_word_table : ∀ j : Fin 27,
    longRootWordSign [0,0,4,4,3,4,3] j=1 ∧
      longRootWordDestination [0,0,4,4,3,4,3] j=coordinateCycleDestination j := by
  decide +kernel

private theorem coordinateCycle_word :
    longRootWordElement (F := F) [0,0,4,4,3,4,3]=coordinateCycle := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply Atlas.Albert.linearMap_ext_basis
  intro c
  obtain ⟨j,hj⟩ := albertCoordinateFinEquiv.symm.surjective c
  change albertCoordinateOfFin j=c at hj
  rw [←hj]
  change (longRootWordElement [0,0,4,4,3,4,3]).val
    (Atlas.Albert.basisVector (albertCoordinateOfFin j)) =
      (coordinateCycle (F := F)).val (Atlas.Albert.basisVector (albertCoordinateOfFin j))
  rw [longRootWordElement_basis,(coordinateCycle_word_table j).1,
    (coordinateCycle_word_table j).2,coordinateCycle_apply,coordinateCycle_basis]
  simp

/-- A four-Weyl-factor expression involving only actual short-root elements. -/
theorem coordinateCycle_rootWord :
    coordinateCycle (F := F)=shortWeylFirstPair 3*shortWeylPair 1 3*(shortWeylFirstPair 0)^2 := by
  have hi : (coordinateCycle (F := F))⁻¹=coordinateCycle^2 := by
    apply inv_eq_of_mul_eq_one_left
    rw [←pow_succ,coordinateCycle_cube]
  rw [←coordinateCycle_word]
  conv_rhs => rw [shortWeylPair_conjugate]
  simp only [longRootWordElement,longRootStepElement]
  simp [hi,pow_two,mul_assoc]

theorem coordinateCycle_mem_rootGenerated : coordinateCycle (F := F)∈rootGenerated := by
  rw [coordinateCycle_rootWord]
  exact (rootGenerated (F := F)).mul_mem
    ((rootGenerated (F := F)).mul_mem (shortWeylFirstPair_mem_rootGenerated 3)
      (shortWeylPair_mem_rootGenerated 1 3))
    ((rootGenerated (F := F)).pow_mem (shortWeylFirstPair_mem_rootGenerated 0) 2)

end Atlas.F4
