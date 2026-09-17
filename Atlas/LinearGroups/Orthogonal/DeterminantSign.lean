import Atlas.LinearGroups.Orthogonal.Special
import Atlas.LinearAlgebra.QuadraticDeterminant
import Atlas.Algebra.SquareOneUnits
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index

/-! # The determinant sign quotient of a polar-nondegenerate quadratic isometry group -/
noncomputable section
open scoped Classical
namespace Atlas.Orthogonal
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)

def determinantSign : isometrySubgroup Q →* rootsOfUnity 2 F where
  toFun g := ⟨determinant Q g, by
    apply (mem_rootsOfUnity 2 _).mpr
    apply Units.ext
    exact Atlas.Quadratic.isometry_det_sq Q hQ (isometryCarrierEquiv Q g)⟩
  map_one' := Subtype.ext (map_one (determinant Q))
  map_mul' g h := Subtype.ext (map_mul (determinant Q) g h)

theorem determinantSign_kernel : (determinantSign Q hQ).ker = specialSubgroup Q := by
  ext g
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

def reflectionElement (a : V) (ha : Q a ≠ 0) : isometrySubgroup Q :=
  (isometryCarrierEquiv Q).symm (Atlas.Quadratic.reflectionIsometry Q a ha)

theorem reflectionElement_determinant (a : V) (ha : Q a ≠ 0) :
    determinant Q (reflectionElement Q a ha) = -1 :=
  Atlas.Quadratic.reflection_det Q a ha

/-- An actual anisotropic reflection realizes the nontrivial sign whenever it exists. -/
theorem determinantSign_surjective (a : V) (ha : Q a ≠ 0) :
    Function.Surjective (determinantSign Q hQ) := by
  intro c
  have hc : c.val.val^2 = (1 : F) := congrArg Units.val ((mem_rootsOfUnity 2 c.val).mp c.prop)
  rcases sq_eq_one_iff.mp hc with h | h
  · refine ⟨1, ?_⟩
    rw [map_one]
    apply Subtype.ext
    apply Units.ext
    exact h.symm
  · refine ⟨reflectionElement Q a ha, ?_⟩
    apply Subtype.ext
    change determinant Q (reflectionElement Q a ha) = c.val
    rw [reflectionElement_determinant]
    apply Units.ext
    exact h.symm

include hQ in
/-- Exact determinant-one kernel index, independent of spinor norms and simplicity. -/
theorem card_special_mul_sign (a : V) (ha : Q a ≠ 0) :
    Nat.card (specialSubgroup Q) * (if (2 : F) = 0 then 1 else 2) = Nat.card (isometrySubgroup Q) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (determinantSign Q hQ).ker
  have he := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (determinantSign Q hQ) (determinantSign_surjective Q hQ a ha)).toEquiv
  rw [he, determinantSign_kernel, Atlas.card_squareOneUnits] at h
  exact (mul_comm _ _).trans h.symm

end Atlas.Orthogonal
