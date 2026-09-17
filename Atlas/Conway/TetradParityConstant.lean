import Atlas.Lattices.LeechSextetSigns

namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators

theorem constant_of_tetrad_parity (c : BinaryWord)
    (hc : ∀ T : Finset Omega, T.card = 4 → tetradSignParity c T = 0) :
    ∀ i j, c i = c j := by
  classical
  intro i j
  by_cases hij : i = j
  · exact congrArg c hij
  have hn : 3 ≤ (Finset.univ \ {i,j} : Finset Omega).card := by
    rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Finset.card_pair hij]
    decide
  obtain ⟨U,hU,hcard⟩ := Finset.exists_subset_card_eq hn
  have hi : i ∉ U := by
    intro h; have := Finset.mem_sdiff.mp (hU h); simp at this
  have hj : j ∉ U := by
    intro h; have := Finset.mem_sdiff.mp (hU h); simp at this
  have hci := hc (insert i U) (by rw [Finset.card_insert_of_notMem hi,hcard])
  have hcj := hc (insert j U) (by rw [Finset.card_insert_of_notMem hj,hcard])
  simp only [tetradSignParity,Finset.sum_coe_sort,Finset.sum_insert hi,Finset.sum_insert hj] at hci hcj
  exact add_right_cancel (hci.trans hcj.symm)

end Atlas.Conway
