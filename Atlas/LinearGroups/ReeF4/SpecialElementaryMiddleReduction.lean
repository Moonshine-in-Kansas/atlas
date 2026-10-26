import Atlas.LinearGroups.ReeF4.SpecialElementaryLowerReduction

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem elementary_reduction_leading19 {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    {u : TraceZero F} (hu : IsSpecialVector m u) (hl : SpecialLeadingAt 19 u) :
    ElementaryReducesToLowest hcard u := by
  obtain ⟨hs,he,hz⟩ := specialVector_negativeC3_descent hcard hu hl.2 hl.1
  apply elementaryReducesToLowest_of_map hcard (negativeC3PivotDescent hcard u)
    (negativeC3PivotDescent_mem_elementary hcard u)
  apply elementary_reduction_leading18 hcard
  refine ⟨?_,hz⟩
  change ((negativeC3PivotDescent hcard u).val u).val.2 2 0≠0
  rw [he]
  exact hl.1

theorem elementary_reduction_leading4 {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    {u : TraceZero F} (hu : IsSpecialVector m u) (hl : SpecialLeadingAt 4 u) :
    ElementaryReducesToLowest hcard u := by
  obtain ⟨hs,he,hz⟩ := specialVector_negativeA2_descent hcard hu hl.2 hl.1
  apply elementaryReducesToLowest_of_map hcard (negativeA2PivotDescent hcard u)
    (negativeA2PivotDescent_mem_elementary hcard u)
  apply elementary_reduction_leading19 hcard hs
  refine ⟨?_,hz⟩
  change ((negativeA2PivotDescent hcard u).val u).val.2 2 1≠0
  rw [he]
  exact hl.1


end Atlas.ReeF4
