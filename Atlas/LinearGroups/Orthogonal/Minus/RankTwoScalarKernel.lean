import Atlas.LinearGroups.Orthogonal.Minus.RankTwoHermitianKernel
import Atlas.LinearGroups.Orthogonal.ProjectiveElementary

/-! The actual Hermitian image has no nonidentity scalar isometries.
This calculation does not use simplicity or orders. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Matrix
variable {K : Type*} [Field K]

theorem hermitian_three_tests_scalar_factor (σ : K ≃+* K)
    (A : Matrix (Fin 2) (Fin 2) K) (hdet : A.det=1) (c : K)
    (hfirst : A * !![1,0;0,0] * kernelDagger σ A = c • !![1,0;0,0])
    (hlast : A * !![0,0;0,1] * kernelDagger σ A = c • !![0,0;0,1])
    (hcross : A * !![0,1;1,0] * kernelDagger σ A = c • !![0,1;1,0]) : c=1 := by
  have haa := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hfirst
  have hcc := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) hfirst
  have hbb := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hlast
  have had := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hcross
  simp [Matrix.mul_apply,Fin.sum_univ_two,kernelDagger] at haa hcc hbb had
  have hc : A 1 0=0 := hcc
  have hb : A 0 1=0 := hbb
  have hdet' : A 0 0 * A 1 1=1 := by simpa [Matrix.det_fin_two,hb,hc] using hdet
  have ha : A 0 0≠0 := by intro h; simp [h] at hdet'
  have had' : A 0 0 * σ (A 1 1)=c := by simpa [hb,hc] using had
  have heq : A 0 0=A 1 1 := σ.injective (mul_left_cancel₀ ha (haa.trans had'.symm))
  have hsq : (A 0 0)^2=1 := by simpa [← heq,pow_two] using hdet'
  rcases sq_eq_one_iff.mp hsq with h | h <;> simpa [h] using haa.symm

section Actual
variable {F : Type*} [Field F] [Finite F] [Finite K] [Algebra F K]
open Atlas.FiniteQuadratic

theorem hermitianHom_scalar_factor (hdeg : Module.finrank F K = 2)
    (g : SpecialLinearGroup (Fin 2) K) (c : F)
    (hscalar : ∀v : Vector 1 F K, (hermitianHom hdeg g).val v = c • v) : c=1 := by
  have hfix (v : Vector 1 F K) :
      g.val * hermitianMatrix v * hermitianDagger (F := F) g.val =
        algebraMap F K c • hermitianMatrix v := by
    rw [← hermitianTransform_intertwine hdeg]
    change hermitianMatrix ((hermitianHom hdeg g).val v) = _
    rw [hscalar,hermitianMatrix_smul]
    ext i j
    simp [Algebra.smul_def]
  apply (algebraMap F K).injective
  rw [map_one]
  apply hermitian_three_tests_scalar_factor (conjugation F K).toRingEquiv g.val g.det_coe
  · simpa [hermitianMatrix,e,kernelDagger,hermitianDagger] using hfix (e (0 : Fin 1),0)
  · simpa [hermitianMatrix,f,kernelDagger,hermitianDagger] using hfix (-f (0 : Fin 1),0)
  · simpa [hermitianMatrix,kernelDagger,hermitianDagger] using hfix (0,1)
end Actual
end Atlas.Orthogonal.Minus
