import Atlas.Fischer.WittDistributions
import Atlas.Mathieu.OctadPairCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

theorem octad_meets_duad_once (a b : Omega) (hab : a ≠ b) :
    (octads.filter (fun O => (a ∈ O ∧ b ∉ O) ∨ (a ∉ O ∧ b ∈ O))).card = 352 := by
  classical
  have h : (octads.filter (fun O => (a ∈ O ∧ b ∉ O) ∨ (a ∉ O ∧ b ∈ O))).card +
      2*(octads.filter (fun O => a ∈ O ∧ b ∈ O)).card =
      (octads.filter (fun O => a ∈ O)).card + (octads.filter (fun O => b ∈ O)).card := by
    simp only [Finset.card_filter,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro O _
    by_cases ha : a ∈ O <;> by_cases hb : b ∈ O <;> simp [ha,hb]
  rw [octads_through_pair_card a b hab,octads_through_point_card,octads_through_point_card] at h
  omega

/-- All three octad intersection frequencies of an arbitrary actual marked duad. -/
theorem octad_duad_distribution (T : Finset Omega) (hT : T.card = 2) :
    octadIntersectionCount T ∅ 2 = 77 ∧ octadIntersectionCount T ∅ 1 = 352 ∧
    octadIntersectionCount T ∅ 0 = 330 := by
  classical
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hT
  have he (O : Finset Omega) : O ∩ {a,b} = ({a,b} : Finset Omega).filter (fun x => x ∈ O) := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_filter]
    tauto
  have h2 : octads.filter (fun O => ∅ ⊆ O ∧ (O ∩ {a,b}).card = 2) =
      octads.filter (fun O => a ∈ O ∧ b ∈ O) := by
    ext O
    by_cases ha : a ∈ O <;> by_cases hb : b ∈ O <;> simp [he,ha,hb,hab,Finset.filter_insert,Finset.filter_singleton]
  have h1 : octads.filter (fun O => ∅ ⊆ O ∧ (O ∩ {a,b}).card = 1) =
      octads.filter (fun O => (a ∈ O ∧ b ∉ O) ∨ (a ∉ O ∧ b ∈ O)) := by
    ext O
    by_cases ha : a ∈ O <;> by_cases hb : b ∈ O <;> simp [he,ha,hb,hab,Finset.filter_insert,Finset.filter_singleton]
  have h0 : octads.filter (fun O => ∅ ⊆ O ∧ (O ∩ {a,b}).card = 0) =
      octads.filter (fun O => a ∉ O ∧ b ∉ O) := by
    ext O
    by_cases ha : a ∈ O <;> by_cases hb : b ∈ O <;> simp [he,ha,hb,hab,Finset.filter_insert,Finset.filter_singleton]
  unfold octadIntersectionCount
  rw [h2,h1,h0,octads_through_pair_card a b hab,octad_meets_duad_once a b hab,
    octads_avoiding_pair_card a b hab]
  exact ⟨rfl,rfl,rfl⟩

end Atlas.Fischer
