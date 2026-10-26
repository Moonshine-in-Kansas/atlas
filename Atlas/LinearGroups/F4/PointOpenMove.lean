import Atlas.LinearGroups.F4.LongRoots
import Atlas.LinearGroups.F4.ParabolicTorus
import Atlas.Algebra.Albert.WhiteCoordinateNonzero

/-! Actual Weyl words move every white vector to the C₇≠0 chart. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert

def pointOpenWitness : Fin 24→List (Fin 5) :=
  ![[4],[2,3,4],[1,3,4],[1,2,4],[0,3,4],[0,2,4],[0,1,4],[4,0],
    [3,4],[2,4],[1,4],[0,4],[0,4,0],[1,4,0],[2,4,0],[3,4,0],
    [],[4,2,4],[4,1,4],[4,0,4],[3,4,0,4],[2,4,1,4],[1,4,2,4],[0]]

theorem pointOpenWitness_correct : ∀ r : Fin 24,
    longRootWordDestination (pointOpenWitness r) ⟨r.val+3,by omega⟩=19 := by
  decide +kernel

variable {F : Type*} [Field F]

theorem exists_basis_to_parabolic (i : Fin 3) (j : Fin 8) :
    ∃ (g : Model F) (s : F), g.val (basisVector (.inr (i,j)))=s • parabolicVector := by
  let r : Fin 24 := ⟨8*i.val+j.val,by omega⟩
  refine ⟨longRootWordElement (pointOpenWitness r),
    (longRootWordSign (pointOpenWitness r) ⟨r.val+3,by omega⟩ : F),?_⟩
  have h := longRootWordElement_basis (F:=F) (pointOpenWitness r) ⟨r.val+3,by omega⟩
  rw [pointOpenWitness_correct] at h
  have hc : albertCoordinateOfFin ⟨r.val+3,by omega⟩ = .inr (i,j) := by
    have hi : (⟨r.val+3,by omega⟩ : Fin 27)=albertCoordinateFinEquiv (.inr (i,j)) := by
      apply Fin.ext
      dsimp [r,albertCoordinateFinEquiv,albertCoordinateToFin]
      omega
    rw [hi]
    change albertCoordinateFinEquiv.symm (albertCoordinateFinEquiv (.inr (i,j))) = _
    exact albertCoordinateFinEquiv.symm_apply_apply _
  rw [hc] at h
  rw [parabolicVector_eq_basis]
  exact h

theorem whiteZero_move_to_open (x : Carrier F) (hx : x≠0)
    (ha : adjoint x=0) (ht : trace x=0) :
    ∃ g : Model F, (g.val x).2 2 7≠0 := by
  obtain ⟨i,j,hij⟩ := whiteZero_exists_offDiagonal x hx ha ht
  obtain ⟨g,s,hg⟩ := exists_basis_to_parabolic (F:=F) i (7-j)
  refine ⟨g,?_⟩
  intro hz
  have h := stabilizer_tracePairing g x (basisVector (.inr (i,7-j)))
  rw [hg,tracePairing_comm,tracePairing_smul_left,tracePairing_comm,
    parabolicVector_eq_basis,tracePairing_octonion_basis,tracePairing_octonion_basis] at h
  have hj : (7-(7-j) : Fin 8)=j := by omega
  simp only [hj] at h
  apply hij
  simpa [hz] using h.symm

end Atlas.F4
