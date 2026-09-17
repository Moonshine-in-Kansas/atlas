import Atlas.LinearGroups.Orthogonal.ElementaryNormal
import Atlas.LinearGroups.Orthogonal.ElementaryTransitivity
import Atlas.LinearGroups.Orthogonal.ReflectionConjugation
import Atlas.LinearGroups.Orthogonal.ReflectionGeneration
import Mathlib.GroupTheory.Commutator.Basic

/-! # The elementary quotient and its reflection images -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (H : WittTwoFrame Q)
  (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

abbrev ElementaryQuotient := isometrySubgroup Q ⧸ elementarySubgroup Q

def elementaryProjection : isometrySubgroup Q →* ElementaryQuotient Q :=
  QuotientGroup.mk' (elementarySubgroup Q)

include H hQ h2 in
/-- Reflections in equal-norm vectors have the same image modulo the actual elementary subgroup. -/
theorem elementaryProjection_reflection_equal_value (a b : V) (ha : Q a ≠ 0)
    (hb : Q b ≠ 0) (hval : Q a = Q b) :
    elementaryProjection Q (reflectionElement Q a ha) =
      elementaryProjection Q (reflectionElement Q b hb) := by
  obtain ⟨g, hg, hga⟩ := elementary_transport_equal_value Q H hQ h2 a b ha hval
  have hg' : elementaryProjection Q g = 1 := by
    change (g : ElementaryQuotient Q) = 1
    exact (QuotientGroup.eq_one_iff g).mpr hg
  have he := congrArg (elementaryProjection Q) (reflectionElement_conj Q g a ha)
  rw [map_mul, map_mul, map_inv, hg', one_mul, inv_one, mul_one] at he
  simpa only [hga] using he

include H hQ h2 in
/-- Every reflection image is central in the elementary quotient. -/
theorem elementaryProjection_reflection_central (a : V) (ha : Q a ≠ 0) :
    elementaryProjection Q (reflectionElement Q a ha) ∈ Subgroup.center (ElementaryQuotient Q) := by
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (elementarySubgroup Q) x
  have hga : Q (g.val a) ≠ 0 := ne_of_eq_of_ne ((isometryCarrierEquiv Q g).map_app a) ha
  have hv := elementaryProjection_reflection_equal_value Q H hQ h2 (g.val a) a hga ha
    ((isometryCarrierEquiv Q g).map_app a)
  have he := congrArg (elementaryProjection Q) (reflectionElement_conj Q g a ha)
  rw [hv, map_mul, map_mul, map_inv] at he
  have ht := congrArg (fun z => z * elementaryProjection Q g) he
  change elementaryProjection Q g * elementaryProjection Q (reflectionElement Q a ha) =
    elementaryProjection Q (reflectionElement Q a ha) * elementaryProjection Q g
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using ht

include H hQ h2 in
/-- Reflection generation and elementary shell transitivity make the quotient abelian. -/
theorem elementaryQuotient_isMulCommutative : IsMulCommutative (ElementaryQuotient Q) := by
  have hr : reflectionSubgroup Q ≤ (Subgroup.center (ElementaryQuotient Q)).comap
      (elementaryProjection Q) := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨a, ha, rfl⟩
    exact elementaryProjection_reflection_central Q H hQ h2 a ha
  rw [reflectionSubgroup_eq_top Q hQ h2] at hr
  apply isMulCommutative_iff.mpr
  intro x y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (elementarySubgroup Q) y
  exact (Subgroup.mem_center_iff.mp (hr (Subgroup.mem_top g))) x

include H hQ h2 in
theorem commutator_le_elementary : commutator (isometrySubgroup Q) ≤ elementarySubgroup Q :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
    (elementaryQuotient_isMulCommutative Q H hQ h2)

end Atlas.Orthogonal
