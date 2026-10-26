import Atlas.LinearGroups.Chevalley.Integral.MinusculePositiveHeight

/-! The integral positive-coroot height evaluates every actual root as twice
its height in the fixed base. No denominator or coefficient-ring assumption. -/

noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- The root height follows from the actual integral simple-root expansion. -/
theorem weightHeight_rootWeight (β : ι) :
    weightHeight P b (rootWeight P β) = 2 * b.height β := by
  obtain ⟨f, _, _, hf⟩ := b.exists_root_eq_sum_int β
  have hexp : rootWeight P β = ∑ i ∈ b.support, f i • rootWeight P i := by
    ext x
    change P.toLinearMap (P.root β) x.val = _
    rw [hf]
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, rootWeight, LinearMap.comp_apply]
    rfl
  rw [hexp]
  change (∑ i ∈ b.support, f i • rootWeight P i) (twiceRhoCoroot P b) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  calc
    (∑ i ∈ b.support, f i * rootWeight P i (twiceRhoCoroot P b)) =
        ∑ i ∈ b.support, f i * 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show rootWeight P i (twiceRhoCoroot P b) = 2 from
        weightHeight_simpleRoot P b ⟨i, hi⟩]
    _ = 2 * b.height β := by
      rw [b.height_eq_sum hf, ← Finset.sum_mul]
      exact mul_comm _ _

end Atlas.Chevalley.Integral.Minuscule
