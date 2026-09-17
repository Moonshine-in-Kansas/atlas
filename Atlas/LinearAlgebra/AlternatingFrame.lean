import Atlas.LinearAlgebra.SymplecticBasis

noncomputable section
namespace Atlas.AlternatingForm
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V)

/-- Independent vectors have a partner dual to the first and orthogonal to the second. -/
theorem exists_dual_partner (hB : B.Nondegenerate) {u v : V} (hu : u ≠ 0)
    (hv : v ∉ Submodule.span F {u}) : ∃ f, B u f = 1 ∧ B v f = 0 := by
  obtain ⟨f,hf⟩ := exists_partner B hB hu
  obtain ⟨w,hw,hvw⟩ : ∃ w, B u w = 0 ∧ B v w ≠ 0 := by
    by_contra! h
    have he : v = (B v f) • u := by
      apply sub_eq_zero.mp
      apply hB.1
      intro x
      have hux : B u (x-(B u x) • f) = 0 := by simp [map_sub,map_smul,hf]
      have hvx := h (x-(B u x) • f) hux
      simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,
        smul_eq_mul] at hvx ⊢
      simpa only [mul_comm] using hvx
    apply hv
    rw [he]
    exact (Submodule.span F {u}).smul_mem _ (Submodule.subset_span (by simp))
  refine ⟨f-(B v f / B v w) • w, ?_, ?_⟩
  · simp [map_sub,map_smul,hw,hf]
  · simp [map_sub,map_smul,hvw]

/-- The first splitting can retain a second independent orthogonal vector in its complement. -/
theorem split_retaining_orthogonal (hA : B.IsAlt) (hB : B.Nondegenerate)
    {u v : V} (hu : u ≠ 0) (hv : v ∉ Submodule.span F {u}) (huv : B u v = 0) :
    ∃ f, B u f = 1 ∧ v ∈ complement B u f := by
  obtain ⟨f,hf,hvf⟩ := exists_dual_partner B hB hu hv
  refine ⟨f,hf,?_,hvf⟩
  change B v u = 0
  rw [← hA.neg_eq u v,huv,neg_zero]
end Atlas.AlternatingForm
