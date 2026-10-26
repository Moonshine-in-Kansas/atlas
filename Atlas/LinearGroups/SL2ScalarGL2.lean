import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.GroupTheory.NoncommCoprod

/-! The concrete scalar-product decomposition GL₂(F) ≃ SL₂(F)×F×
over a finite field of characteristic two. This generic matrix result is
independent of the Ree construction and uses the existing Frobenius equivalence. -/
noncomputable section
namespace Atlas
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The concrete map (A,c) ↦ cA. -/
def sl2ScalarToGL : Matrix.SpecialLinearGroup (Fin 2) F × Fˣ →*
    Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.SpecialLinearGroup.toGL.noncommCoprod
    (Matrix.GeneralLinearGroup.scalar (Fin 2))
    (fun A c => (Matrix.GeneralLinearGroup.scalar_commute c
      (Matrix.SpecialLinearGroup.toGL A)).symm)

theorem sl2ScalarToGL_apply (A : Matrix.SpecialLinearGroup (Fin 2) F) (c : Fˣ) :
    sl2ScalarToGL (A,c) = Matrix.SpecialLinearGroup.toGL A *
      Matrix.GeneralLinearGroup.scalar (Fin 2) c := rfl

theorem sl2ScalarToGL_matrix (A : Matrix.SpecialLinearGroup (Fin 2) F) (c : Fˣ) :
    (sl2ScalarToGL (A,c) : Matrix (Fin 2) (Fin 2) F) = (c : F) • (A : Matrix (Fin 2) (Fin 2) F) := by
  change (A : Matrix (Fin 2) (Fin 2) F) * Matrix.scalar (Fin 2) (c : F) = _
  rw [Matrix.scalar_apply]
  exact (Matrix.smul_eq_mul_diagonal _ _).symm

theorem sl2ScalarToGL_det (A : Matrix.SpecialLinearGroup (Fin 2) F) (c : Fˣ) :
    Matrix.GeneralLinearGroup.det (sl2ScalarToGL (A,c)) = c^2 := by
  rw [sl2ScalarToGL_apply, map_mul, Matrix.SpecialLinearGroup.coeToGL_det,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, one_mul]

theorem sl2ScalarToGL_injective : Function.Injective (sl2ScalarToGL (F := F)) := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨A,c⟩ h
  have hc2 : c^2 = 1 := by
    have hd := congrArg Matrix.GeneralLinearGroup.det h
    simpa only [sl2ScalarToGL_det, map_one] using hd
  have hc : c = 1 := by
    apply Units.ext
    apply (frobeniusEquiv F 2).injective
    change (c : F)^2 = (1 : F)^2
    have hh := congrArg (fun z : Fˣ => (z : F)) hc2
    simpa using hh
  have hA : A = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    simpa only [sl2ScalarToGL_apply, hc, map_one, mul_one] using h
  exact Prod.ext hA hc

theorem sl2ScalarToGL_surjective : Function.Surjective (sl2ScalarToGL (F := F)) := by
  intro B
  obtain ⟨c,hc⟩ := (Units.mapEquiv (frobeniusEquiv F 2).toMulEquiv).surjective
    (Matrix.GeneralLinearGroup.det B)
  have hc2 : c^2 = Matrix.GeneralLinearGroup.det B := by
    apply Units.ext
    have hh := congrArg (fun z : Fˣ => (z : F)) hc
    change (c : F)^2 = ((Matrix.GeneralLinearGroup.det B : Fˣ) : F) at hh
    change (c : F)^2 = ((Matrix.GeneralLinearGroup.det B : Fˣ) : F)
    exact hh
  let H : Matrix.GeneralLinearGroup (Fin 2) F :=
    B * (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹
  have hH : Matrix.GeneralLinearGroup.det H = 1 := by
    change Matrix.GeneralLinearGroup.det
      (B * (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹) = 1
    rw [map_mul, map_inv, Matrix.GeneralLinearGroup.det_scalar,
      Fintype.card_fin, hc2, mul_inv_cancel]
  let A : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨(H : Matrix (Fin 2) (Fin 2) F), by
      exact congrArg (fun z : Fˣ => (z : F)) hH⟩
  have hA : Matrix.SpecialLinearGroup.toGL A = H := by
    apply Units.ext
    rfl
  refine ⟨(A,c),?_⟩
  rw [sl2ScalarToGL_apply,hA]
  change B * (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ *
    Matrix.GeneralLinearGroup.scalar (Fin 2) c = B
  rw [mul_assoc,inv_mul_cancel,mul_one]

/-- Actual matrix isomorphism, with forward map (A,c) ↦ cA. -/
def sl2ScalarGL2Equiv : Matrix.SpecialLinearGroup (Fin 2) F × Fˣ ≃*
    Matrix.GeneralLinearGroup (Fin 2) F :=
  MulEquiv.ofBijective sl2ScalarToGL ⟨sl2ScalarToGL_injective,sl2ScalarToGL_surjective⟩

theorem sl2ScalarGL2Equiv_apply (A : Matrix.SpecialLinearGroup (Fin 2) F) (c : Fˣ) :
    sl2ScalarGL2Equiv (A,c) = Matrix.SpecialLinearGroup.toGL A *
      Matrix.GeneralLinearGroup.scalar (Fin 2) c := rfl

end Atlas
