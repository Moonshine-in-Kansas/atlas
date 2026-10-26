import Atlas.LinearGroups.ReeF4.PositiveRootOrderedCollection
import Atlas.LinearGroups.ReeF4.AlternatingRootWordInjective

noncomputable section
namespace Atlas.ReeF4
open Atlas.GroupTheory
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem positiveRootSubgroup_range_eq {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Set.range (fun p : (Fin 4 → F) × (Fin 4 → F × F) => alternatingRootWord hcard p.1 p.2) =
      (positiveRootSubgroup hcard : Set (Model F m)) := by
  rw [alternatingRootWord_range_eq_orderedProduct,
    orderedSubgroupProduct_eq_join _ (positiveRoot_hasOrderedCollection hcard),
    positiveRootFactorList_join]

/-- Actual twelve-parameter normal form for the generated positive-root subgroup. -/
def positiveRootParameters {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    ((Fin 4 → F) × (Fin 4 → F × F)) ≃ positiveRootSubgroup hcard :=
  (Equiv.ofInjective _ (alternatingRootWord_injective hcard)).trans
    (Equiv.setCongr (positiveRootSubgroup_range_eq hcard))

theorem card_positiveRootSubgroup {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Nat.card (positiveRootSubgroup hcard) = (Nat.card F)^12 := by
  rw [← Nat.card_congr (positiveRootParameters hcard)]
  simp only [Nat.card_prod, Nat.card_fun, Nat.card_fin]
  ring

end Atlas.ReeF4
