import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Pullback of actual polynomials by matrices. This keeps polynomial equality
distinct from equality of functions over a finite field. -/
noncomputable section
namespace Atlas.PolynomialLinear
open Matrix MvPolynomial
variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [CommRing F]

def substitute (M : Matrix ι ι F) : MvPolynomial ι F →+* MvPolynomial ι F :=
  eval₂Hom C (M.map C *ᵥ X)

@[simp] theorem substitute_C (M : Matrix ι ι F) (r : F) :
    substitute M (C r) = C r := by simp [substitute]

@[simp] theorem substitute_X (M : Matrix ι ι F) (i : ι) :
    substitute M (X i) = (M.map C *ᵥ X) i := by simp [substitute]

@[simp] theorem substitute_one (p : MvPolynomial ι F) : substitute (1 : Matrix ι ι F) p = p := by
  have he : substitute (1 : Matrix ι ι F) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i
      rw [substitute_X, Matrix.map_one _ (map_zero C) (map_one C), Matrix.one_mulVec]
      rfl
  exact congrArg (fun f : MvPolynomial ι F →+* MvPolynomial ι F => f p) he

theorem substitute_mul (M N : Matrix ι ι F) (p : MvPolynomial ι F) :
    substitute (M * N) p = substitute N (substitute M p) := by
  have he : substitute (M * N) = (substitute N).comp (substitute M) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i
      simp only [RingHom.comp_apply, substitute_X, Matrix.mulVec, dotProduct,
        Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul, substitute_C,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_assoc _ _ _
  exact congrArg (fun f : MvPolynomial ι F →+* MvPolynomial ι F => f p) he

theorem eval_substitute (M : Matrix ι ι F) (x : ι → F) (p : MvPolynomial ι F) :
    eval x (substitute M p) = eval (M *ᵥ x) p := by
  have he : (eval x).comp (substitute M) = eval (M *ᵥ x) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; simp [substitute, Matrix.mulVec, dotProduct]
  exact congrArg (fun f : MvPolynomial ι F →+* F => f p) he

def stabilizer (p : MvPolynomial ι F) : Subgroup (GeneralLinearGroup ι F) where
  carrier := {g | substitute g.val p = p}
  one_mem' := substitute_one p
  mul_mem' {g h} hg hh := by
    change substitute (g.val * h.val) p = p
    rw [substitute_mul, hg, hh]
  inv_mem' {g} hg := by
    have h := substitute_mul g.val g.inv p
    rw [g.val_inv, substitute_one, hg] at h
    exact h.symm

theorem eval₂_substitute {R : Type*} [CommRing R] (f : F →+* R)
    (M : Matrix ι ι F) (x : ι → R) (p : MvPolynomial ι F) :
    eval₂Hom f x (substitute M p) = eval₂Hom f (M.map f *ᵥ x) p := by
  have he : (eval₂Hom f x).comp (substitute M) = eval₂Hom f (M.map f *ᵥ x) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; simp [substitute, Matrix.mulVec, dotProduct]
  exact congrArg (fun h : MvPolynomial ι F →+* R => h p) he

end Atlas.PolynomialLinear
