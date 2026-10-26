import Atlas.LinearGroups.Chevalley.RootData.RootWordLabels
import Atlas.LinearGroups.Chevalley.RootData.RootWeylLongest

/-! Any reduced expression of the actual longest Weyl element enumerates all
positive root labels exactly once. This does not identify their root subgroups. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

theorem rootWordLabels_longest_toFinset (l : List b.support)
    (hred : IsReducedRootWord P b l)
    (hw : rootWeylWord P b l = rootWeylLongest P b) :
    (rootWordLabels P b l).toFinset = Finset.univ.filter (fun β : ι => b.IsPos β) := by
  apply Finset.eq_of_subset_of_card_le
  · intro β hβ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ β,
      isReducedRootWord_labels_positive P b l hred (List.mem_toFinset.mp hβ)⟩
  · rw [List.toFinset_card_of_nodup (isReducedRootWord_labels_nodup P b l hred),
      rootWordLabels_length]
    have hlen : rootWeylLength P b (rootWeylLongest P b) = l.length := by
      rw [← hw]
      exact hred
    rw [rootWeylLength_longest] at hlen
    exact hlen.le

theorem rootWordLabels_longest_mem_iff (l : List b.support)
    (hred : IsReducedRootWord P b l)
    (hw : rootWeylWord P b l = rootWeylLongest P b) (β : ι) :
    β ∈ rootWordLabels P b l ↔ b.IsPos β := by
  rw [← List.mem_toFinset, rootWordLabels_longest_toFinset P b l hred hw]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every positive root occurs at exactly one position of any reduced longest word. -/
theorem rootWordLabelAt_longest_existsUnique (l : List b.support)
    (hred : IsReducedRootWord P b l)
    (hw : rootWeylWord P b l = rootWeylLongest P b) {β : ι} (hβ : b.IsPos β) :
    ∃! k : Fin l.length, rootWordLabelAt P b l k = β := by
  have hmem := (rootWordLabels_longest_mem_iff P b l hred hw β).mpr hβ
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hmem
  let j : Fin l.length := ⟨k.val, by simpa only [rootWordLabels_length] using k.isLt⟩
  have hj : rootWordLabelAt P b l j = β := by
    simpa only [rootWordLabelAt, j] using hk
  refine ⟨j, hj, ?_⟩
  intro j' hj'
  exact isReducedRootWord_labelAt_injective P b l hred (hj'.trans hj.symm)

end Atlas.Chevalley.RootData
