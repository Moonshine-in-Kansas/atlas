import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2CompanionRootRelations
import Atlas.GroupTheory.NormalCommutatorPropagation

/-! Normal-subgroup propagation in the actual selected C2 companion.
The coefficient-one mixed relation transfers containment from the entire
positive short-root subgroup to the entire positive long-root subgroup.
This uses neither division by two nor faithfulness of the adjoint projection. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo.C2Minuscule
open scoped commutatorElement
local instance c2NormalContinuationRankNeZero : NeZero C2.rank := ⟨by decide⟩

variable {R : Type*} [CommRing R]

theorem companion_Z_mem_normal_of_Xshort
    (H : Subgroup (Companion R)) [H.Normal]
    (hshort : ∀ u : R, selectedWeightCompanionX C2 R 0 u ∈ H) (t : R) :
    rootZ t ∈ H :=
  (inferInstance : H.Normal).conj_mem _ (hshort t) (weyl 1)

/-- Only short-root containment is a premise; long-root containment is derived
from the actual mixed commutator with short parameter one. -/
theorem companion_Xlong_mem_normal_of_Xshort
    (H : Subgroup (Companion R)) [H.Normal]
    (hshort : ∀ u : R, selectedWeightCompanionX C2 R 0 u ∈ H) (t : R) :
    selectedWeightCompanionX C2 R 1 t ∈ H := by
  have hrelation :
      ⁅selectedWeightCompanionX C2 R 0 1,
        selectedWeightCompanionX C2 R 1 t⁆ =
      rootZ (-t) * (weyl 0 * selectedWeightCompanionX C2 R 1 t * (weyl 0)⁻¹) := by
    change ⁅selectedWeightCompanionX C2 R 0 1,
      selectedWeightCompanionX C2 R 1 t⁆ = rootZ (-t) * rootW t
    simpa only [neg_one_mul, one_pow, one_mul] using
      (companion_short_long_commutator (1 : R) t)
  exact Atlas.GroupTheory.mem_normal_of_commutator_eq_mul_conjugate H
    (selectedWeightCompanionX C2 R 0 1) (selectedWeightCompanionX C2 R 1 t)
    (rootZ (-t)) (weyl 0) (selectedWeightCompanionX C2 R 1 t)
    (hshort 1) (companion_Z_mem_normal_of_Xshort H hshort (-t)) hrelation

theorem companion_W_mem_normal_of_Xshort
    (H : Subgroup (Companion R)) [H.Normal]
    (hshort : ∀ u : R, selectedWeightCompanionX C2 R 0 u ∈ H) (t : R) :
    rootW t ∈ H :=
  (inferInstance : H.Normal).conj_mem _
    (companion_Xlong_mem_normal_of_Xshort H hshort t) (weyl 0)

theorem companion_W_mem_commutator_of_Xshort
    (hshort : ∀ u : R, selectedWeightCompanionX C2 R 0 u ∈
      commutator (Companion R)) (t : R) :
    rootW t ∈ commutator (Companion R) :=
  companion_W_mem_normal_of_Xshort (commutator (Companion R)) hshort t

theorem companion_Xlong_mem_commutator_of_Xshort
    (hshort : ∀ u : R, selectedWeightCompanionX C2 R 0 u ∈
      commutator (Companion R)) (t : R) :
    selectedWeightCompanionX C2 R 1 t ∈ commutator (Companion R) :=
  companion_Xlong_mem_normal_of_Xshort (commutator (Companion R)) hshort t

variable {G : Type*} [Group G]

/-- The higher-rank application needs an actual group homomorphism, but no
injectivity, surjectivity or identification of its kernel. -/
theorem companion_image_Xlong_mem_normal_of_Xshort
    (f : Companion R →* G) (H : Subgroup G) [H.Normal]
    (hshort : ∀ u : R, f (selectedWeightCompanionX C2 R 0 u) ∈ H) (t : R) :
    f (selectedWeightCompanionX C2 R 1 t) ∈ H :=
  companion_Xlong_mem_normal_of_Xshort (H.comap f) hshort t

theorem companion_image_W_mem_normal_of_Xshort
    (f : Companion R →* G) (H : Subgroup G) [H.Normal]
    (hshort : ∀ u : R, f (selectedWeightCompanionX C2 R 0 u) ∈ H) (t : R) :
    f (rootW t) ∈ H :=
  companion_W_mem_normal_of_Xshort (H.comap f) hshort t

theorem companion_image_Xlong_mem_commutator_of_Xshort
    (f : Companion R →* G)
    (hshort : ∀ u : R, f (selectedWeightCompanionX C2 R 0 u) ∈ commutator G)
    (t : R) : f (selectedWeightCompanionX C2 R 1 t) ∈ commutator G :=
  companion_image_Xlong_mem_normal_of_Xshort f (commutator G) hshort t

end Atlas.Chevalley.Integral.RankTwo.C2Minuscule
