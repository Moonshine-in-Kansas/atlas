import Atlas.LinearGroups.Chevalley.Comparison.TypeASpecialLinearHom
import Atlas.LinearAlgebra.SLAdjacentGeneration

/-! The new type-A companion maps onto the existing SL matrix group.
Surjectivity uses the actual marked adjacent root images, without counting. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeA

theorem specialLinearHom_surjective (r : ℕ) (hr : 1 ≤ r)
    (K : Type*) [Field K] : Function.Surjective (specialLinearHom r hr K) := by
  have htop : (specialLinearHom r hr K).range = ⊤ := by
    apply Atlas.sl_eq_top_of_adjacent_transvections hr
    · intro i hi t
      exact ⟨selectedWeightCompanionX (.A r hr) K i t, specialLinearHom_X r hr K i t⟩
    · intro i hi t
      exact ⟨selectedWeightCompanionY (.A r hr) K i t, specialLinearHom_Y r hr K i t⟩
  exact MonoidHom.range_eq_top.mp htop

end Atlas.Chevalley.Comparison.TypeA
