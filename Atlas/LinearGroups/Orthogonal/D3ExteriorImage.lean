import Atlas.LinearGroups.Orthogonal.D3ExteriorAction
import Atlas.LinearGroups.Orthogonal.IntrinsicStandard
import Atlas.LinearGroups.Orthogonal.FullDicksonD
import Atlas.LinearGroups.Elementary

/-! # The genuine SL₄ exterior-square image lies in the actual elementary D₃ group -/
noncomputable section
namespace Atlas.Orthogonal.D3Exterior
variable {F : Type*} [Field F] [Finite F]

/-- Perfectness of the source places its image in the independently identified intrinsic kernel. -/
theorem toOrthogonal_mem_elementary (g : Matrix.SpecialLinearGroup (Fin 4) F) :
    toOrthogonal g ∈ elementarySubgroup (formD 3 F) := by
  letI := Atlas.sl_perfect (F := F) 4 (by decide)
  letI := Group.IsPerfect.range (toOrthogonal (F := F))
  have hr : toOrthogonal g ∈ (toOrthogonal (F := F)).range := ⟨g,rfl⟩
  rw [← Subgroup.commutator_eq_self (H := (toOrthogonal (F := F)).range)] at hr
  have hc : toOrthogonal g ∈ commutator (O_DPlus 3 F) :=
    Subgroup.commutator_mono le_top le_top hr
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    rw [← fullDicksonD_kernel_elementary 0]
    exact Abelianization.commutator_subset_ker (fullDicksonD 0) hc
  · rw [elementaryD_eq_commutator 1 h2]
    exact hc

def toElementary : Matrix.SpecialLinearGroup (Fin 4) F →* elementarySubgroup (formD 3 F) :=
  toOrthogonal.codRestrict _ toOrthogonal_mem_elementary

end Atlas.Orthogonal.D3Exterior
