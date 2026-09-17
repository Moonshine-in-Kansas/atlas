import Atlas.LinearGroups.Orthogonal.SiegelReflections
import Atlas.LinearGroups.Orthogonal.DicksonReflectionD
import Atlas.LinearGroups.Orthogonal.DicksonEvenReflectionKernel

/-! # Stable split-D elementary groups satisfy the intrinsic Dickson condition

All field characteristics are included. No equality between the elementary and
Dickson kernels, and no full-group reflection generation, is assumed here.
-/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F]

theorem elementaryD_le_reflections_stable (n : ℕ) :
    elementarySubgroup (formD (n + 3) F) ≤ reflectionSubgroup (formD (n + 3) F) := by
  apply elementary_le_reflections_stable _ polarD_nondegenerate
  simp only [VectorD, Index, Module.finrank_pi, Module.finrank_self, Fintype.card_sum,
    Fintype.card_fin, mul_one]
  omega

theorem dicksonValue_elementaryD_stable (n : ℕ) (g : O_DPlus (n + 3) F)
    (hg : g ∈ elementarySubgroup (formD (n + 3) F)) : dicksonValue (formD (n + 3) F) g = 0 := by
  apply dicksonValue_elementary_stable _ polarD_nondegenerate _ g hg
  simp only [VectorD, Index, Module.finrank_pi, Module.finrank_self, Fintype.card_sum,
    Fintype.card_fin, mul_one]
  omega

/-- The actual inclusion in the reflection subgroup, without changing the elementary carrier. -/
def elementaryDReflectionHom (n : ℕ) :
    elementarySubgroup (formD (n + 3) F) →* reflectionSubgroup (formD (n + 3) F) :=
  Subgroup.inclusion (elementaryD_le_reflections_stable n)

theorem elementaryDReflectionHom_injective (n : ℕ) :
    Function.Injective (elementaryDReflectionHom (F := F) n) :=
  Subgroup.inclusion_injective (elementaryD_le_reflections_stable n)

theorem elementaryDReflectionHom_character (n : ℕ)
    (g : elementarySubgroup (formD (n + 3) F)) :
    splitDReflectionCharacter (elementaryDReflectionHom n g) = 1 := by
  apply Multiplicative.toAdd.injective
  exact dicksonValue_elementaryD_stable n g.val g.prop

/-- The stable elementary split-D group lies in the actual normal even-reflection kernel. -/
theorem elementaryD_le_evenReflections_stable (n : ℕ) :
    elementarySubgroup (formD (n + 3) F) ≤ evenReflectionSubgroup (formD (n + 3) F) := by
  intro g hg
  exact (mem_evenReflection_iff _ polarD_nondegenerate g).mpr
    ⟨elementaryD_le_reflections_stable n hg, dicksonValue_elementaryD_stable n g hg⟩
end Atlas.Orthogonal
