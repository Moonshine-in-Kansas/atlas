import Atlas.LinearGroups.F4.OppositeCellSpanning
import Atlas.LinearGroups.F4.WhiteZeroPoints

/-! Fixing every actual opposite-cell vector forces an Albert automorphism to be
identity, also in characteristic three. Diagonal vectors are recovered by adjoints. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

set_option maxHeartbeats 1000000 in
private theorem oppositePair_adjoint (i : Fin 3) :
    adjoint (basisVector (.inr (i,0))+basisVector (.inr (i,7)) : Carrier F)=
      -basisVector (.inl i) := by
  fin_cases i
  all_goals
    apply Prod.ext
    · ext j; fin_cases j <;> simp [adjoint,basisVector,SplitOctonion.norm]
    · ext j k; fin_cases j <;> fin_cases k <;>
        simp [adjoint,basisVector,SplitOctonion.mul,SplitOctonion.conjugate,
          SplitOctonion.trace,SplitOctonion.unit]

theorem oppositeCell_kernel_trivial (g : Model F)
    (hg : ∀x : OppositeCell F,g.val x.val=x.val) : g=1 := by
  have hchart (a : F) (u v : Fin 4→F) (z : Fin 6→F) :
      g.val (oppositeZeroChart a u v z)=oppositeZeroChart a u v z :=
    hg ⟨oppositeZeroChart a u v z,oppositeZeroChart_adjoint _ _ _ _,
      oppositeZeroChart_trace _ _ _ _,oppositeZeroChart_C7 _ _ _ _⟩
  have hoff (i : Fin 3) (j : Fin 8) :
      g.val (basisVector (.inr (i,j)))=basisVector (.inr (i,j)) := by
    rw [←oppositeOffCombination_basis]
    fin_cases i <;> fin_cases j <;>
      simp [oppositeOffCombination,cellOrigin,cellU,cellV,cellZ,cellUZ,cellVZ,cellZZ,
        _root_.map_add,_root_.map_sub,_root_.map_neg,hchart]
  have hdiag (i : Fin 3) : g.val (basisVector (.inl i))=basisVector (.inl i) := by
    have h := stabilizer_adjoint g (basisVector (.inr (i,0))+basisVector (.inr (i,7)))
    rw [_root_.map_add,hoff,hoff,oppositePair_adjoint,_root_.map_neg] at h
    exact (neg_injective h).symm
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply linearMap_ext_basis
  intro i
  cases i with
  | inl i => exact hdiag i
  | inr i => exact hoff i.1 i.2

theorem oppositeCell_action_ext (g h : Model F)
    (he : ∀x : OppositeCell F,g.val x.val=h.val x.val) : g=h := by
  have hz : h⁻¹*g=1 := by
    apply oppositeCell_kernel_trivial
    intro x
    change h.val.symm (g.val x.val)=x.val
    rw [he,h.val.symm_apply_apply]
  exact (inv_mul_eq_one.mp hz).symm

end Atlas.F4
