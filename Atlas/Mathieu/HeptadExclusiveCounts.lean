import Atlas.Mathieu.HeptadMarkedIntersectionCounts
import Atlas.Combinatorics.ColoredIncidenceCount

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable
local instance exclusiveHeptadPointsFintype (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _

theorem heptad_exclusive_count_balance (a : Omega) (p j : Mathieu23Points a)
    (hpj : p ≠ j) (D : Finset (Mathieu23Points a)) (hD : D ∈ mathieu23Blocks a)
    (s t : ℕ) (hst : (s = 1 ∧ t = 3) ∨ (s = 3 ∧ t = 1)) :
    ((mathieu23Blocks a).filter (fun E =>
      (p ∈ E ∧ j ∉ E ∧ (D ∩ E).card = s) ∨
      (p ∉ E ∧ j ∈ E ∧ (D ∩ E).card = t))).card +
      (21 - if p ∈ D ∧ j ∈ D then 1 else 0) =
    ((mathieu23Blocks a).filter (fun E => p ∈ E ∧ (D ∩ E).card = s)).card +
    ((mathieu23Blocks a).filter (fun E => j ∈ E ∧ (D ∩ E).card = t)).card := by
  let S := (mathieu23Blocks a).erase D
  have hs7 : s ≠ 7 := by rcases hst with h | h <;> omega
  have ht7 : t ≠ 7 := by rcases hst with h | h <;> omega
  have hne : s ≠ t := by rcases hst with h | h <;> omega
  have hi (E : Finset (Mathieu23Points a)) (hE : E ∈ mathieu23Blocks a) (hED : E ≠ D) :
      (D ∩ E).card = s ∨ (D ∩ E).card = t := by
    have h := mathieu23_heptad_intersection a D E hD hE (Ne.symm hED)
    rcases hst with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact h
    · exact h.symm
  have hf1 : S.filter (fun E => p ∈ E ∧ (D ∩ E).card = s) =
      (mathieu23Blocks a).filter (fun E => p ∈ E ∧ (D ∩ E).card = s) := by
    ext E
    by_cases hE : E ∈ mathieu23Blocks a <;> by_cases hED : E = D
    all_goals simp_all [S,Finset.mem_filter,Finset.mem_erase,mathieu23Blocks_size a D hD,Ne.symm hs7]
  have hf2 : S.filter (fun E => j ∈ E ∧ ¬(D ∩ E).card = s) =
      (mathieu23Blocks a).filter (fun E => j ∈ E ∧ (D ∩ E).card = t) := by
    ext E
    by_cases hE : E ∈ mathieu23Blocks a
    · by_cases hED : E = D
      · subst E; simp [S,hD,mathieu23Blocks_size a D hD,Ne.symm ht7]
      · rcases hi E hE hED with hh | hh <;> simp [S,hE,hED,hh,hne,Ne.symm hne]
    · simp [S,hE]
  have hfg : S.filter (fun E => (p ∈ E ∧ j ∉ E ∧ (D ∩ E).card = s) ∨
        (p ∉ E ∧ j ∈ E ∧ ¬(D ∩ E).card = s)) =
      (mathieu23Blocks a).filter (fun E => (p ∈ E ∧ j ∉ E ∧ (D ∩ E).card = s) ∨
        (p ∉ E ∧ j ∈ E ∧ (D ∩ E).card = t)) := by
    ext E
    by_cases hE : E ∈ mathieu23Blocks a
    · by_cases hED : E = D
      · subst E; simp [S,hD,mathieu23Blocks_size a D hD,Ne.symm hs7,Ne.symm ht7]
      · rcases hi E hE hED with hh | hh <;> simp [S,hE,hED,hh,hne,Ne.symm hne]
    · simp [S,hE]
  have hboth : (S.filter (fun E => p ∈ E ∧ j ∈ E)).card =
      21 - if p ∈ D ∧ j ∈ D then 1 else 0 := by
    have he : S.filter (fun E => p ∈ E ∧ j ∈ E) =
        ((mathieu23Blocks a).filter (fun E => p ∈ E ∧ j ∈ E)).erase D := by
      ext E; simp [S]; tauto
    rw [he]
    have hc := mathieu23Blocks_through_pair_card a p j hpj
    by_cases hh : p ∈ D ∧ j ∈ D
    · have hm : D ∈ (mathieu23Blocks a).filter (fun E => p ∈ E ∧ j ∈ E) := by simp [hD,hh]
      rw [Finset.card_erase_of_mem hm,hc,if_pos hh]
    · have hm : D ∉ (mathieu23Blocks a).filter (fun E => p ∈ E ∧ j ∈ E) := by simp [hD,hh]
      rw [Finset.erase_eq_of_notMem hm,hc,if_neg hh,Nat.sub_zero]
  have hh := Atlas.Combinatorics.colored_incidence_count S
    (fun E => p ∈ E) (fun E => j ∈ E) (fun E => (D ∩ E).card = s)
  simp only [hfg,hboth,hf1,hf2] at hh
  convert hh using 1
  congr 1
  apply congrArg Finset.card
  ext E
  simpa only [Finset.mem_filter] using (Finset.ext_iff.mp hfg E).symm

end Atlas.Codes
