import Atlas.Codes.TernaryGolayTriads

namespace Atlas.Codes

/-- The actual constant weight-six words of the fixed ternary code, recorded by support. -/
def ternaryConstantHexads : Finset (Finset (Fin 12)) :=
  (Finset.univ.powersetCard 6).filter (fun s =>
    ternaryEncoder (ternaryDecoder (ternaryTriadWord s)) = ternaryTriadWord s)

theorem mem_ternaryConstantHexads (s : Finset (Fin 12)) :
    s ∈ ternaryConstantHexads ↔ s.card = 6 ∧ ternaryTriadWord s ∈ ternaryGolay := by
  simp [ternaryConstantHexads, ternaryGolay_mem_iff_decode]

/-- A bounded check of the actual twelve-coordinate code, not a group certificate. -/
theorem ternaryConstantHexads_card : ternaryConstantHexads.card = 22 := by
  decide +kernel

theorem ternaryConstantHexads_compl (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) : sᶜ ∈ ternaryConstantHexads := by
  obtain ⟨hc, hw⟩ := (mem_ternaryConstantHexads s).mp hs
  apply (mem_ternaryConstantHexads _).mpr
  constructor
  · simp [Finset.card_compl, hc]
  · have he : ternaryTriadWord sᶜ = (1 : TernaryWord) - ternaryTriadWord s := by
      ext i
      by_cases hi : i ∈ s <;> simp [ternaryTriadWord, hi]
    rw [he]
    exact ternaryGolay.sub_mem ternaryGolay_one hw

theorem ternaryConstantHexads_permute (g : TernaryPureAutomorphism)
    (s : Finset (Fin 12)) (hs : s ∈ ternaryConstantHexads) :
    s.map g.val.toEmbedding ∈ ternaryConstantHexads := by
  obtain ⟨hc, hw⟩ := (mem_ternaryConstantHexads s).mp hs
  apply (mem_ternaryConstantHexads _).mpr
  exact ⟨by simpa using hc, by rw [ternaryTriadWord_permute]; exact g.property _ hw⟩

end Atlas.Codes
