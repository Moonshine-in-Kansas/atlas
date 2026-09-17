import Atlas.LinearGroups.G2.LongRootNormalGeneration
import Atlas.LinearGroups.G2.TorusNormalization
import Mathlib.GroupTheory.IsPerfect

namespace Atlas.G2
open Atlas.SplitOctonion Explicit
open scoped commutatorElement
variable {F : Type*} [Field F]

theorem rootA_neg (a : F) : rootA (-a) = (rootA a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [rootA_add,neg_add_cancel,rootA_zero]

theorem rootA_mem_commutator (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (a:F) :
    rootA a ∈ commutator (Model F) := by
  let u : Fˣ := Units.mk0 t ht0
  have he : ⁅torus u 1,rootA (a/(t-1))⁆ = rootA a := by
    rw [commutatorElement_def,torus_rootA,← rootA_neg,rootA_add]
    congr 1
    change (t*1)*(a/(t-1)) + -(a/(t-1)) = a
    field_simp
    ring
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem isPerfect [Finite F] (hq : 2 < Nat.card F) : Group.IsPerfect (Model F) := by
  classical
  let := Fintype.ofFinite F
  have hc : ({0,1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [Nat.card_eq_fintype_card] using hq
  obtain ⟨t,_,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have ht' : t ≠ 0 ∧ t ≠ 1 := by simpa using ht
  constructor
  apply normal_eq_top_of_unipotent
  exact unipotent_le_normal_of_rootA _ (rootA_mem_commutator t ht'.1 ht'.2)
    t ht'.1 ht'.2
end Atlas.G2
