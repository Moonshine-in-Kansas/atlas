import Atlas.LinearGroups.Orthogonal.Minus.RankTwoHermitianKernel

/-! Explicit special-linear transport on singular lines in the actual four-dimensional minus space. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic Matrix
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem hermitian_singular_line_transport (hdeg : Module.finrank F K = 2)
    (u : Vector 1 F K) (hun : u ≠ 0) (hu : form hdeg 1 u = 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) K, ∃ c : F, c ≠ 0 ∧
      (hermitianHom hdeg g).val (e (0 : Fin 1),0) = c • u := by
  have hq : u.1 (.inl 0)*u.1 (.inr 0)+norm F K u.2=0 := by
    simpa [form_apply,formD_apply,Fin.sum_univ_one] using hu
  by_cases hx : u.1 (.inl 0)=0
  · have hz : u.2=0 := (norm_zero_iff hdeg u.2).mp (by simpa [hx] using hq)
    have hy : u.1 (.inr 0)≠0 := by
      intro hy
      apply hun
      apply Prod.ext
      · funext i
        cases i with
        | inl i => fin_cases i; exact hx
        | inr i => fin_cases i; exact hy
      · exact hz
    let g : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
    refine ⟨g,-(u.1 (.inr 0))⁻¹,neg_ne_zero.mpr (inv_ne_zero hy),?_⟩
    change hermitianTransform g.val (e 0,0) = _
    apply Prod.ext
    · funext i
      cases i with
      | inl i => fin_cases i; simp [hermitianTransform,g,e,hx]
      | inr i => fin_cases i; simp [hermitianTransform,g,e,hy]
    · simp [hermitianTransform,g,e,hz]
  · let s : K := conjugation F K u.2 / algebraMap F K (u.1 (.inl 0))
    let g : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1,0;s,1],by simp [Matrix.det_fin_two]⟩
    refine ⟨g,(u.1 (.inl 0))⁻¹,inv_ne_zero hx,?_⟩
    apply hermitianMatrix_injective
    change hermitianMatrix (hermitianTransform g.val (e 0,0)) = _
    rw [hermitianTransform_intertwine hdeg]
    have hxK : algebraMap F K (u.1 (.inl 0))≠0 := (map_ne_zero (algebraMap F K)).mpr hx
    have hqK := congrArg (algebraMap F K) hq
    simp only [map_add,map_mul,map_zero,norm_formula hdeg] at hqK
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianMatrix,hermitianDagger,g,s,e,Matrix.mul_apply,Fin.sum_univ_two,
        Algebra.smul_def,vecHead,vecTail,map_mul,conjugation_conjugation hdeg] <;>
      field_simp [hxK] <;> first | (solve | ring) | linear_combination hqK

end Atlas.Orthogonal.Minus
