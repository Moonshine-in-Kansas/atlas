import Atlas.Algebra.SplitOctonion.Automorphism
import Atlas.Algebra.SplitOctonion.BasisChecks
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Coefficient extension of concrete split-octonion automorphisms. The field
homomorphism need not be surjective. Invertible coefficient matrices are mapped
through the existing general linear group functor; multiplicativity is checked
on the standard basis and then extended bilinearly. -/
namespace Atlas.SplitOctonion.Extension
open Matrix

section Rings
variable {F K : Type*} [CommRing F] [CommRing K]

def coefficients (φ : F →+* K) (x : Carrier F) : Carrier K := fun i=>φ (x i)

@[simp] theorem coefficients_basis (φ : F →+* K) (i : Fin 8) :
    coefficients φ (basisVector i)=basisVector i := by
  ext j
  by_cases h : j=i <;> simp [coefficients,basisVector,Pi.single_apply,h]

@[simp] theorem coefficients_mul (φ : F →+* K) (x y : Carrier F) :
    coefficients φ (mul x y)=mul (coefficients φ x) (coefficients φ y) := by
  ext i
  fin_cases i <;> simp [coefficients,mul]

end Rings

section Fields
variable {F K : Type*} [Field F] [Field K]

noncomputable def matrixEquiv (F : Type*) [Field F] :
    Matrix.GeneralLinearGroup (Fin 8) F ≃* (Carrier F ≃ₗ[F] Carrier F) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Carrier F))

noncomputable def extendLinear (φ : F →+* K) :
    (Carrier F ≃ₗ[F] Carrier F) →* (Carrier K ≃ₗ[K] Carrier K) :=
  (matrixEquiv K).toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.map φ).comp (matrixEquiv F).symm.toMonoidHom)

theorem extendLinear_coefficients (φ : F →+* K) (g : Carrier F ≃ₗ[F] Carrier F)
    (x : Carrier F) : extendLinear φ g (coefficients φ x)=coefficients φ (g x) := by
  change (φ.mapMatrix (LinearMap.toMatrix' g.toLinearMap)) *ᵥ (fun i=>φ (x i))=
    (fun i=>φ (g x i))
  ext i
  exact (φ.map_mulVec (LinearMap.toMatrix' g.toLinearMap) x i).symm.trans
    (congrArg φ (congrFun (LinearMap.toMatrix'_mulVec g.toLinearMap x) i))

theorem extendLinear_multiplicative (φ : F →+* K) (g : Automorphism F) :
    ∀x y : Carrier K,extendLinear φ g.val (mul x y)=
      mul (extendLinear φ g.val x) (extendLinear φ g.val y) := by
  apply map_mul_of_basis (extendLinear φ g.val).toLinearMap
  intro i j
  change extendLinear φ g.val (mul (basisVector i) (basisVector j))=
    mul (extendLinear φ g.val (basisVector i)) (extendLinear φ g.val (basisVector j))
  rw [←coefficients_basis φ i,←coefficients_basis φ j,←coefficients_mul,
    extendLinear_coefficients,automorphism_mul,coefficients_mul,
    extendLinear_coefficients,extendLinear_coefficients]

/-- Actual scalar extension of the full octonion automorphism group. -/
noncomputable def extend (φ : F →+* K) : Automorphism F →* Automorphism K where
  toFun g := ⟨extendLinear φ g.val,extendLinear_multiplicative φ g⟩
  map_one' := Subtype.ext (map_one (extendLinear φ))
  map_mul' g h := Subtype.ext (map_mul (extendLinear φ) g.val h.val)

theorem extend_coefficients (φ : F →+* K) (g : Automorphism F) (x : Carrier F) :
    (extend φ g).val (coefficients φ x)=coefficients φ (g.val x) :=
  extendLinear_coefficients φ g.val x

theorem extend_injective (φ : F →+* K) : Function.Injective (extend φ) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  apply φ.injective
  have hx := congrArg (fun a : Automorphism K=>a.val (coefficients φ x)) he
  rw [extend_coefficients,extend_coefficients] at hx
  exact congrFun hx i

theorem extend_trace (φ : F →+* K) (g : Automorphism F) (x : Carrier K) :
    trace ((extend φ g).val x)=trace x := automorphism_trace _ _

theorem extend_norm (φ : F →+* K) (g : Automorphism F) (x : Carrier K) :
    norm ((extend φ g).val x)=norm x := automorphism_norm _ _

end Fields
end Atlas.SplitOctonion.Extension
