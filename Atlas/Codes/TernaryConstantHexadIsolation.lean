import Atlas.Codes.TernaryConstantHexads

namespace Atlas.Codes
open scoped BigOperators

/-- A codeword supported on a constant hexad and one additional point vanishes
at that additional point, by orthogonality to the complementary hexad. -/
theorem ternaryConstantHexad_isolated_coordinate (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (w : ternaryGolay) (j : Fin 12) (hj : j ∉ s)
    (hw : ∀ i,i ∉ s → i≠j → w.val i=0) : w.val j=0 := by
  classical
  have hc := ((mem_ternaryConstantHexads sᶜ).mp (ternaryConstantHexads_compl s hs)).2
  have ho := ternaryGolay_selfOrthogonal w.property (ternaryTriadWord sᶜ) hc
  have he : ∀ i,ternaryTriadWord sᶜ i*w.val i = if i=j then w.val j else 0 := by
    intro i
    by_cases hij : i=j
    · subst i; simp [ternaryTriadWord,hj]
    · by_cases hi : i ∈ s
      · simp [ternaryTriadWord,hi,hij]
      · simp [ternaryTriadWord,hi,hij,hw i hi hij]
  change (∑ i,ternaryTriadWord sᶜ i*w.val i)=0 at ho
  simp_rw [he] at ho
  simpa using ho

end Atlas.Codes
