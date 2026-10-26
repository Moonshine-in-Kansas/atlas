import Atlas.LinearGroups.F4.CoordinateCycleGenerated
import Atlas.LinearGroups.F4.PointOpenMove

/-! The open-cell reduction uses the actual root-generated subgroup. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

theorem longRootStepElement_mem_rootGenerated (i : Fin 5) :
    longRootStepElement (F:=F) i∈rootGenerated := by
  fin_cases i
  · exact shortWeylFirstPair_mem_rootGenerated 0
  · exact shortWeylFirstPair_mem_rootGenerated 1
  · exact shortWeylFirstPair_mem_rootGenerated 2
  · exact shortWeylFirstPair_mem_rootGenerated 3
  · exact coordinateCycle_mem_rootGenerated

theorem longRootWordElement_mem_rootGenerated (w : List (Fin 5)) :
    longRootWordElement (F:=F) w∈rootGenerated := by
  induction w with
  | nil => exact (rootGenerated (F:=F)).one_mem
  | cons i w ih =>
    exact (rootGenerated (F:=F)).mul_mem ih (longRootStepElement_mem_rootGenerated i)

theorem exists_basis_to_parabolic_generated (i : Fin 3) (j : Fin 8) :
    ∃ (g : Model F), g∈rootGenerated ∧
      ∃s : F, g.val (basisVector (.inr (i,j)))=s • parabolicVector := by
  let r : Fin 24 := ⟨8*i.val+j.val,by omega⟩
  refine ⟨longRootWordElement (pointOpenWitness r),
    longRootWordElement_mem_rootGenerated _,
    (longRootWordSign (pointOpenWitness r) ⟨r.val+3,by omega⟩ : F),?_⟩
  have h := longRootWordElement_basis (F:=F) (pointOpenWitness r) ⟨r.val+3,by omega⟩
  rw [pointOpenWitness_correct] at h
  have hc : albertCoordinateOfFin ⟨r.val+3,by omega⟩ = .inr (i,j) := by
    have hi : (⟨r.val+3,by omega⟩ : Fin 27)=albertCoordinateFinEquiv (.inr (i,j)) := by
      apply Fin.ext
      dsimp [r,albertCoordinateFinEquiv,albertCoordinateToFin]
      omega
    rw [hi]
    exact albertCoordinateFinEquiv.symm_apply_apply _
  rw [hc] at h
  rw [parabolicVector_eq_basis]
  exact h

theorem whiteZero_move_to_open_generated (x : Carrier F) (hx : x≠0)
    (ha : adjoint x=0) (ht : trace x=0) :
    ∃ g : Model F, g∈rootGenerated ∧ (g.val x).2 2 7≠0 := by
  obtain ⟨i,j,hij⟩ := whiteZero_exists_offDiagonal x hx ha ht
  obtain ⟨g,hgmem,s,hg⟩ := exists_basis_to_parabolic_generated (F:=F) i (7-j)
  refine ⟨g,hgmem,?_⟩
  intro hz
  have h := stabilizer_tracePairing g x (basisVector (.inr (i,7-j)))
  rw [hg,tracePairing_comm,tracePairing_smul_left,tracePairing_comm,
    parabolicVector_eq_basis,tracePairing_octonion_basis,tracePairing_octonion_basis] at h
  have hj : (7-(7-j) : Fin 8)=j := by omega
  simp only [hj] at h
  apply hij
  simpa [hz] using h.symm

end Atlas.F4
