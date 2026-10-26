import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.Module

/-! Rational orthogonal reflections preserving an integral lattice through modular glue. -/
namespace Atlas.Lattices
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def reflectionMap (P : V →ₗ[ℚ] V) : V →ₗ[ℚ] V := (2 : ℚ) • P - LinearMap.id

theorem reflectionMap_involutive (P : V →ₗ[ℚ] V) (hP : ∀v,P (P v)=P v) :
    Function.Involutive (reflectionMap P) := by
  intro v
  change (2 : ℚ) • P ((2 : ℚ) • P v-v)-((2 : ℚ) • P v-v)=v
  rw [map_sub,map_smul,hP]
  module

def reflectionEquiv (P : V →ₗ[ℚ] V) (hP : ∀v,P (P v)=P v) : V ≃ₗ[ℚ] V :=
  { reflectionMap P with
    invFun := reflectionMap P
    left_inv := reflectionMap_involutive P hP
    right_inv := reflectionMap_involutive P hP }

theorem reflectionMap_pairing (B : LinearMap.BilinForm ℚ V)
    (P : V →ₗ[ℚ] V) (hP : ∀v,P (P v)=P v)
    (hself : ∀v w,B (P v) w=B v (P w)) (v w : V) :
    B (reflectionMap P v) (reflectionMap P w)=B v w := by
  change B ((2 : ℚ) • P v-v) ((2 : ℚ) • P w-w)=_
  simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
  rw [hself v (P w),hP w,hself v w]
  ring

/-- The duality condition is imposed only in the projection range, not its complement. -/
theorem reflectionMap_lattice_mem
    (B : LinearMap.BilinForm ℚ V) (L M : Submodule ℤ V) (hML : M≤L)
    (hL : ∀v∈L,∀w∈L,∃k : ℤ,B v w=(k : ℚ))
    (P : V →ₗ[ℚ] V) (hself : ∀v w,B (P v) w=B v (P w))
    (hfix : ∀w∈M,P w=w)
    (hmod : ∀v∈LinearMap.range P,(∀w∈M,∃k : ℤ,B v w=(k : ℚ)) → (2 : ℚ) • v∈M)
    (v : V) (hv : v∈L) : reflectionMap P v∈L := by
  apply L.sub_mem
  · apply hML
    apply hmod (P v) ⟨v,rfl⟩
    intro w hw
    rw [hself,hfix w hw]
    exact hL v hv w (hML hw)
  · exact hv

theorem reflectionEquiv_lattice_iff
    (B : LinearMap.BilinForm ℚ V) (L M : Submodule ℤ V) (hML : M≤L)
    (hL : ∀v∈L,∀w∈L,∃k : ℤ,B v w=(k : ℚ))
    (P : V →ₗ[ℚ] V) (hP : ∀v,P (P v)=P v)
    (hself : ∀v w,B (P v) w=B v (P w)) (hfix : ∀w∈M,P w=w)
    (hmod : ∀v∈LinearMap.range P,(∀w∈M,∃k : ℤ,B v w=(k : ℚ)) → (2 : ℚ) • v∈M)
    (v : V) : reflectionEquiv P hP v∈L ↔ v∈L := by
  constructor
  · intro h
    have hh := reflectionMap_lattice_mem B L M hML hL P hself hfix hmod _ h
    change reflectionMap P (reflectionMap P v)∈L at hh
    rwa [reflectionMap_involutive P hP v] at hh
  · exact reflectionMap_lattice_mem B L M hML hL P hself hfix hmod v

end Atlas.Lattices
