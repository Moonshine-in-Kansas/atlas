import Atlas.Codes.TernarySyndromePartition
set_option maxRecDepth 10000

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem ternaryOrientedSyndrome_action (g : TernaryPureAutomorphism)
    (p : TernaryOrientedTriad) : g • ternaryOrientedSyndrome p =
      ternaryOrientedSyndrome (ternaryOrientedMap g.val p) := by
  apply Subtype.ext
  change ternarySyndromePermutation g (ternarySyndromeClass (ternaryOrientedWord p.val)) =
    ternarySyndromeClass (ternaryOrientedWord (ternaryOrientedMap g.val p).val)
  rw [ternarySyndromePermutation_class, ternaryOrientedMap_word]

theorem ternaryOrientedSyndromes_transitive (c d : TernaryAffineSyndrome)
    (hc : c ∈ ternaryOrientedSyndromes) (hd : d ∈ ternaryOrientedSyndromes) :
    ∃ g : TernaryPureAutomorphism, g • c = d := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨g, hg⟩ := ternaryOriented_transitive p q
  exact ⟨g, by rw [ternaryOrientedSyndrome_action, hg]⟩

theorem ternaryOrientedSyndromes_preserved (g : TernaryPureAutomorphism)
    (c : TernaryAffineSyndrome) (hc : c ∈ ternaryOrientedSyndromes) :
    g • c ∈ ternaryOrientedSyndromes := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hc
  rw [ternaryOrientedSyndrome_action]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

theorem ternaryOrientedSyndromes_orbit (c : TernaryAffineSyndrome)
    (hc : c ∈ ternaryOrientedSyndromes) :
    MulAction.orbit TernaryPureAutomorphism c = {d | d ∈ ternaryOrientedSyndromes} := by
  ext d
  constructor
  · rintro ⟨g, rfl⟩
    exact ternaryOrientedSyndromes_preserved g c hc
  · intro hd
    exact ternaryOrientedSyndromes_transitive c d hc hd

end Atlas.Codes
