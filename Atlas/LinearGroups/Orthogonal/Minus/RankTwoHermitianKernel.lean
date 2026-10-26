import Atlas.LinearGroups.Orthogonal.Minus.RankTwoHermitian
import Atlas.LinearGroups.ProjectiveSpecialLinear
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Three concrete Hermitian test matrices determine the scalar kernel.
This helper is independent of a choice of basis for the quadratic extension. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Matrix
variable {K : Type*} [Field K]

def kernelDagger (σ : K ≃+* K) (A : Matrix (Fin 2) (Fin 2) K) := A.transpose.map σ

theorem hermitian_three_tests_scalar (σ : K ≃+* K)
    (A : Matrix (Fin 2) (Fin 2) K) (hdet : A.det=1)
    (hfirst : A * !![1,0;0,0] * kernelDagger σ A = !![1,0;0,0])
    (hlast : A * !![0,0;0,1] * kernelDagger σ A = !![0,0;0,1])
    (hcross : A * !![0,1;1,0] * kernelDagger σ A = !![0,1;1,0]) :
    ∃ a : K, a^2=1 ∧ Matrix.scalar (Fin 2) a = A := by
  have haa := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hfirst
  have hcc := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) hfirst
  have hbb := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hlast
  have had := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hcross
  simp [Matrix.mul_apply,Fin.sum_univ_two,kernelDagger] at haa hcc hbb had
  have hc : A 1 0=0 := hcc
  have hb : A 0 1=0 := hbb
  have ha : A 0 0≠0 := by intro h; simp [h] at haa
  have had' : A 0 0 * σ (A 1 1)=1 := by simpa [hb,hc] using had
  have heq : A 0 0=A 1 1 := σ.injective (mul_left_cancel₀ ha (haa.trans had'.symm))
  have hsq : (A 0 0)^2=1 := by
    simpa [Matrix.det_fin_two,hb,hc,← heq,pow_two] using hdet
  refine ⟨A 0 0,hsq,?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar,Matrix.diagonal,hb,hc,heq]

theorem hermitian_scalar_congruence (σ : K ≃+* K) (a : K) (ha : a^2=1)
    (M : Matrix (Fin 2) (Fin 2) K) :
    Matrix.scalar (Fin 2) a * M * kernelDagger σ (Matrix.scalar (Fin 2) a) = M := by
  rcases sq_eq_one_iff.mp ha with h | h <;> subst a <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kernelDagger,Matrix.scalar,Matrix.diagonal,Matrix.mul_apply,Fin.sum_univ_two]

/-- Generic quotient interface once the concrete three-test calculation identifies the kernel. -/
def hermitianProjectiveOfKernel {G : Type*} [Group G]
    (ρ : Matrix.SpecialLinearGroup (Fin 2) K →* G)
    (hker : ρ.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K →* G :=
  QuotientGroup.lift _ ρ (le_of_eq hker.symm)

theorem hermitianProjectiveOfKernel_injective {G : Type*} [Group G]
    (ρ : Matrix.SpecialLinearGroup (Fin 2) K →* G)
    (hker : ρ.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) :
    Function.Injective (hermitianProjectiveOfKernel ρ hker) :=
  (QuotientGroup.injective_lift_iff _ ρ (le_of_eq hker.symm)).mpr hker.symm
section Actual
variable {F : Type*} [Field F] [Finite F] [Finite K] [Algebra F K]
open Atlas.FiniteQuadratic

theorem hermitianHom_kernel (hdeg : Module.finrank F K = 2) :
    (hermitianHom hdeg).ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
  ext g
  rw [MonoidHom.mem_ker, Matrix.SpecialLinearGroup.mem_center_iff]
  simp only [Fintype.card_fin]
  constructor
  · intro hg
    have hfix (v : Vector 1 F K) :
        g.val * hermitianMatrix v * hermitianDagger (F := F) g.val = hermitianMatrix v := by
      rw [← hermitianTransform_intertwine hdeg]
      have hv := congrArg (fun h : O hdeg 1 => h.val v) hg
      exact congrArg hermitianMatrix hv
    apply hermitian_three_tests_scalar (conjugation F K).toRingEquiv g.val g.det_coe
    · simpa [hermitianMatrix,e,kernelDagger,hermitianDagger] using
        hfix (e (0 : Fin 1),0)
    · simpa [hermitianMatrix,f,kernelDagger,hermitianDagger] using
        hfix (-f (0 : Fin 1),0)
    · simpa [hermitianMatrix,kernelDagger,hermitianDagger] using hfix (0,1)
  · rintro ⟨a,ha,hg⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply hermitianMatrix_injective
    change hermitianMatrix (hermitianTransform g.val v) = hermitianMatrix v
    rw [hermitianTransform_intertwine hdeg,← hg]
    exact hermitian_scalar_congruence (conjugation F K).toRingEquiv a ha (hermitianMatrix v)

def hermitianProjectiveHom (hdeg : Module.finrank F K = 2) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K →* O hdeg 1 :=
  hermitianProjectiveOfKernel (hermitianHom hdeg) (hermitianHom_kernel hdeg)

theorem hermitianProjectiveHom_injective (hdeg : Module.finrank F K = 2) :
    Function.Injective (hermitianProjectiveHom hdeg) :=
  hermitianProjectiveOfKernel_injective (hermitianHom hdeg) (hermitianHom_kernel hdeg)

@[simp] theorem hermitianProjectiveHom_mk (hdeg : Module.finrank F K = 2)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    hermitianProjectiveHom hdeg (QuotientGroup.mk g) = hermitianHom hdeg g := rfl
end Actual
end Atlas.Orthogonal.Minus

