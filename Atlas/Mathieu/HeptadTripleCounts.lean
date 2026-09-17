import Atlas.Mathieu.HeptadPairCounts
import Atlas.Combinatorics.SteinerTripleCount

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable
local instance heptadTriplePointsFintype (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _

theorem mathieu23Blocks_through_triple_card (a : Omega) (b c d : Mathieu23Points a)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ((mathieu23Blocks a).filter (fun B => b ∈ B ∧ c ∈ B ∧ d ∈ B)).card = 5 := by
  have hv : Fintype.card (Mathieu23Points a) = 23 := by
    rw [← Nat.card_eq_fintype_card,mathieu23_degree]
  have hh := Atlas.Combinatorics.steiner_four_triple_count (mathieu23Blocks a)
    hv (mathieu23Blocks_size a) (mathieu23_steiner a) {b,c,d} (by simp [hbc,hbd,hcd])
  simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using hh

end Atlas.Codes
