import Atlas.LinearGroups.F4.OppositeCellSpanning
import Atlas.Algebra.Albert.WhiteCoordinateNonzero

/-! A common-opposite witness relative to the marked C₀ point. The proof uses
only actual opposite-cell vectors and their linear span, with no finite-field
count, order, or simplicity input. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

private def pairingWith (y : Carrier F) : Carrier F →ₗ[F] F where
  toFun x := tracePairing y x
  map_add' x z := by
    rw [tracePairing_comm,tracePairing_add_left,tracePairing_comm x,tracePairing_comm z]
  map_smul' a x := by
    change tracePairing y (a • x)=a*tracePairing y x
    rw [tracePairing_comm,tracePairing_smul_left,tracePairing_comm x]

theorem oppositeCell_pairing_detects_offDiagonal (y : Carrier F)
    (hy : ∀z : OppositeCell F, tracePairing y z.val=0) : ∀i j, y.2 i j=0 := by
  let L : Carrier F →ₗ[F] F := pairingWith y
  have hchart (a : F) (u v : Fin 4→F) (z : Fin 6→F) :
      L (oppositeZeroChart a u v z)=0 :=
    hy ⟨oppositeZeroChart a u v z,oppositeZeroChart_adjoint _ _ _ _,
      oppositeZeroChart_trace _ _ _ _,oppositeZeroChart_C7 _ _ _ _⟩
  have hoff (i : Fin 3) (j : Fin 8) : L (basisVector (.inr (i,j)))=0 := by
    rw [←oppositeOffCombination_basis]
    fin_cases i <;> fin_cases j <;>
      simp [oppositeOffCombination,cellOrigin,cellU,cellV,cellZ,cellUZ,cellVZ,cellZZ,
        _root_.map_add,_root_.map_sub,_root_.map_neg,hchart]
  intro i j
  have h : tracePairing y (basisVector (.inr (i,7-j)))=0 := hoff i (7-j)
  rw [tracePairing_octonion_basis] at h
  simpa using h

theorem whiteZero_common_opposite (y : Carrier F) (hy : y≠0)
    (ha : adjoint y=0) (ht : trace y=0) :
    ∃z : OppositeCell F, tracePairing y z.val≠0 := by
  by_contra hn
  push_neg at hn
  obtain ⟨i,j,hij⟩ := whiteZero_exists_offDiagonal y hy ha ht
  exact hij (oppositeCell_pairing_detects_offDiagonal y hn i j)

end Atlas.F4
