import Atlas.LinearGroups.G2.BinarySign
import Atlas.LinearGroups.G2.LongA2Commutator
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Abelianization.Defs

/-! Direct derived-subgroup identification, independent of the unitary bridge.
The long A2 commutator has coefficient one, including in characteristic two. -/
namespace Atlas.G2
open Explicit
open scoped commutatorElement
variable {F : Type*} [Field F]

/-- The normal closure of the long roots is perfect even over F2. -/
theorem longRootNormalClosure_perfect : Group.IsPerfect (longRootNormalClosure (F := F)) := by
  let H := longRootNormalClosure (F := F)
  have hA (a : F) : rootA a ∈ H :=
    Subgroup.subset_normalClosure (rootA_mem_longRootLocal a)
  have hB (a : F) : rootB a ∈ H :=
    Subgroup.subset_normalClosure (rootB_mem_longRootLocal a)
  have hE (a : F) : rootE a ∈ H := by
    rw [← weylS_rootB]
    exact (inferInstance : H.Normal).conj_mem _ (hB a) _
  have hcA (a : F) : rootA a ∈ ⁅H,H⁆ := by
    rw [← one_mul a, ← rootB_rootE_commutator]
    exact Subgroup.commutator_mem_commutator (hB 1) (hE a)
  have hcB (a : F) : rootB a ∈ ⁅H,H⁆ := by
    rw [← weylR_rootA]
    exact (inferInstance : (⁅H,H⁆ : Subgroup (Model F)).Normal).conj_mem _ (hcA a) _
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_left H H)
  change Subgroup.normalClosure _ ≤ ⁅H,H⁆
  apply Subgroup.normalClosure_le_normal
  rintro g ⟨p,rfl⟩
  exact (⁅H,H⁆ : Subgroup (Model F)).mul_mem (hcA p.toAdd.1) (hcB p.toAdd.2)

namespace BinaryException

theorem commutator_eq_H : commutator (Model K) = H := by
  apply le_antisymm
  · rw [← lineSign_kernel]
    exact Abelianization.commutator_subset_ker Binary.lineSign
  · haveI := longRootNormalClosure_perfect (F := K)
    rw [← Subgroup.commutator_eq_self (H := H)]
    exact Subgroup.commutator_mono le_top le_top

theorem commutator_eq_lineSign_kernel : commutator (Model K) = Binary.lineSign.ker := by
  rw [commutator_eq_H, lineSign_kernel]

theorem card_commutator : Nat.card (commutator (Model K)) = 6048 := by
  rw [commutator_eq_H]
  exact card_H

theorem index_commutator : (commutator (Model K)).index = 2 := by
  rw [commutator_eq_H]
  exact index_H

end BinaryException
end Atlas.G2
