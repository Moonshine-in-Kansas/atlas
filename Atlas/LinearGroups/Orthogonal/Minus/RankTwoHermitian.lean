import Atlas.LinearGroups.Orthogonal.Minus.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! Actual four-dimensional norm-tail space in two-by-two Hermitian coordinates. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic Matrix
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

abbrev HermitianMat (K : Type*) := Matrix (Fin 2) (Fin 2) K

def hermitianMatrix (v : Vector 1 F K) : HermitianMat K :=
  !![algebraMap F K (v.1 (.inl 0)),v.2;
    conjugation F K v.2,-algebraMap F K (v.1 (.inr 0))]

theorem hermitianMatrix_injective : Function.Injective (hermitianMatrix (F := F) (K := K)) := by
  intro v w h
  apply Prod.ext
  · funext i
    cases i with
    | inl i =>
      fin_cases i
      exact (algebraMap F K).injective (congrArg (fun M => M 0 0) h)
    | inr i =>
      fin_cases i
      apply (algebraMap F K).injective
      exact neg_injective (congrArg (fun M => M 1 1) h)
  · exact congrArg (fun M => M 0 1) h

theorem hermitianMatrix_add (v w : Vector 1 F K) :
    hermitianMatrix (v+w) = hermitianMatrix v + hermitianMatrix w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianMatrix,map_add,add_comm]

theorem hermitianMatrix_smul (c : F) (v : Vector 1 F K) :
    hermitianMatrix (c • v) = c • hermitianMatrix v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianMatrix,Algebra.smul_def,map_mul]

def hermitianCoordinates : Vector 1 F K →ₗ[F] HermitianMat K where
  toFun := hermitianMatrix
  map_add' := hermitianMatrix_add
  map_smul' := hermitianMatrix_smul

theorem hermitianMatrix_det (hdeg : Module.finrank F K = 2) (v : Vector 1 F K) :
    (hermitianMatrix v).det = -algebraMap F K (form hdeg 1 v) := by
  simp [hermitianMatrix,Matrix.det_fin_two,form_apply,formD_apply,
    norm_formula hdeg]
  ring

def hermitianDagger (A : HermitianMat K) : HermitianMat K :=
  A.transpose.map (conjugation F K)

theorem hermitianDagger_mul (A B : HermitianMat K) :
    hermitianDagger (F := F) (A*B) = hermitianDagger (F := F) B * hermitianDagger (F := F) A := by
  ext i j
  simp [hermitianDagger,Matrix.mul_apply,map_mul,mul_comm]

theorem hermitianDagger_one : hermitianDagger (F := F) (1 : HermitianMat K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianDagger]

/-- The diagonal entries are explicitly F-valued by norm and trace formulas. -/
def hermitianTransform (A : HermitianMat K) (v : Vector 1 F K) : Vector 1 F K :=
  (Sum.elim
    (fun _ => norm F K (A 0 0)*v.1 (.inl 0) - norm F K (A 0 1)*v.1 (.inr 0) +
      trace F K (A 0 0*v.2*conjugation F K (A 0 1)))
    (fun _ => -norm F K (A 1 0)*v.1 (.inl 0) + norm F K (A 1 1)*v.1 (.inr 0) -
      trace F K (A 1 0*v.2*conjugation F K (A 1 1))),
    A 0 0*algebraMap F K (v.1 (.inl 0))*conjugation F K (A 1 0) -
    A 0 1*algebraMap F K (v.1 (.inr 0))*conjugation F K (A 1 1) +
    A 0 0*v.2*conjugation F K (A 1 1) +
    A 0 1*conjugation F K v.2*conjugation F K (A 1 0))

theorem hermitianTransform_intertwine (hdeg : Module.finrank F K = 2)
    (A : HermitianMat K) (v : Vector 1 F K) :
    hermitianMatrix (hermitianTransform A v) = A*hermitianMatrix v*hermitianDagger (F := F) A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianMatrix,hermitianTransform,hermitianDagger,Matrix.mul_apply,
      Fin.sum_univ_succ,norm_formula hdeg,trace_formula hdeg,map_add,map_sub,map_mul,
      conjugation_conjugation hdeg] <;> ring

theorem hermitianTransform_one (hdeg : Module.finrank F K = 2) (v : Vector 1 F K) :
    hermitianTransform (1 : HermitianMat K) v = v := by
  apply hermitianMatrix_injective
  rw [hermitianTransform_intertwine hdeg,hermitianDagger_one,one_mul,mul_one]

theorem hermitianTransform_mul (hdeg : Module.finrank F K = 2)
    (A B : HermitianMat K) (v : Vector 1 F K) :
    hermitianTransform (A*B) v = hermitianTransform A (hermitianTransform B v) := by
  apply hermitianMatrix_injective
  simp only [hermitianTransform_intertwine hdeg,hermitianDagger_mul,mul_assoc]

def hermitianAction (hdeg : Module.finrank F K = 2)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : Vector 1 F K ≃ₗ[F] Vector 1 F K where
  toFun := hermitianTransform g.val
  invFun := hermitianTransform g⁻¹.val
  left_inv v := by
    rw [← hermitianTransform_mul hdeg,← SpecialLinearGroup.coe_mul,
      inv_mul_cancel,SpecialLinearGroup.coe_one,hermitianTransform_one hdeg]
  right_inv v := by
    rw [← hermitianTransform_mul hdeg,← SpecialLinearGroup.coe_mul,
      mul_inv_cancel,SpecialLinearGroup.coe_one,hermitianTransform_one hdeg]
  map_add' v w := by
    apply hermitianMatrix_injective
    simp only [hermitianTransform_intertwine hdeg,hermitianMatrix_add,mul_add,add_mul]
  map_smul' c v := by
    apply hermitianMatrix_injective
    simp only [hermitianTransform_intertwine hdeg,hermitianMatrix_smul,
      Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply]

theorem hermitianAction_preserves (hdeg : Module.finrank F K = 2)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : Vector 1 F K) :
    form hdeg 1 (hermitianAction hdeg g v) = form hdeg 1 v := by
  apply (algebraMap F K).injective
  apply neg_injective
  rw [← hermitianMatrix_det hdeg,← hermitianMatrix_det hdeg]
  change (hermitianMatrix (hermitianTransform g.val v)).det = _
  rw [hermitianTransform_intertwine hdeg,Matrix.det_mul,Matrix.det_mul,g.det_coe,one_mul]
  have hd : (hermitianDagger (F := F) g.val).det = 1 := by
    calc
      _ = conjugation F K g.val.det := by
        simp only [hermitianDagger,Matrix.det_fin_two,Matrix.map_apply,Matrix.transpose_apply,map_sub,map_mul]
        ring
      _ = 1 := by rw [g.det_coe,map_one]
  rw [hd,mul_one]

def hermitianHom (hdeg : Module.finrank F K = 2) :
    Matrix.SpecialLinearGroup (Fin 2) K →* O hdeg 1 where
  toFun g := ⟨hermitianAction hdeg g,hermitianAction_preserves hdeg g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact hermitianTransform_one hdeg
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact hermitianTransform_mul hdeg g.val h.val v

end Atlas.Orthogonal.Minus
