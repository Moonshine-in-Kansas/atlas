import Atlas.Algebra.BinaryQuadraticCode
import Mathlib.LinearAlgebra.Basis.Bilinear

namespace Atlas.Algebra
open Atlas.Codes
open scoped BigOperators

/-- Bilinear contraction with an arbitrary word and bilinear form. -/
def binaryBilinearContraction {V : Type*} [AddCommGroup V] [Module Bit V] [Fintype V]
    (w : V → Bit) (B : V →ₗ[Bit] V →ₗ[Bit] Bit) : V →ₗ[Bit] V →ₗ[Bit] Bit where
  toFun s := {
    toFun t := ∑ v, w v * B s v * B t v
    map_add' t u := by simp [map_add,mul_add,Finset.sum_add_distrib]
    map_smul' a t := by
      simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring }
  map_add' s t := by
    ext u
    change (∑ v, w v * B (s+t) v * B u v) =
      (∑ v, w v * B s v * B u v)+(∑ v, w v * B t v * B u v)
    simp [map_add,mul_add,add_mul,Finset.sum_add_distrib]
  map_smul' a s := by
    ext t
    change (∑ v, w v * B (a • s) v * B t v) = a * ∑ v, w v * B s v * B t v
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring


theorem binaryBilinear_eq_of_basis
    {F G : BinaryFour →ₗ[Bit] BinaryFour →ₗ[Bit] Bit}
    (h : ∀ i j : Fin 4, F (Pi.single i 1) (Pi.single j 1)=G (Pi.single i 1) (Pi.single j 1)) : F=G := by
  apply LinearMap.ext_basis (Pi.basisFun Bit (Fin 4)) (Pi.basisFun Bit (Fin 4))
  intro i j
  simpa only [Pi.basisFun_apply] using h i j

end Atlas.Algebra
