import Atlas.Conway.Co3TriangleParameterMap

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def signedSupportNegative (T : Finset Omega) (s : T → Bit) : Finset Omega :=
  (support s).image Subtype.val

theorem signedSupportNegative_mem (T : Finset Omega) (s : T → Bit) (i : Omega) :
    i ∈ signedSupportNegative T s ↔ ∃ h : i ∈ T, s ⟨i,h⟩ ≠ 0 := by
  simp only [signedSupportNegative,Finset.mem_image,support,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨j,hj⟩,hs,he⟩
    change j = i at he
    subst j
    exact ⟨hj,hs⟩
  · rintro ⟨hi,hs⟩
    exact ⟨⟨i,hi⟩,hs,rfl⟩

theorem signedSupportNegative_subset (T : Finset Omega) (s : T → Bit) :
    signedSupportNegative T s ⊆ T := fun i hi => ((signedSupportNegative_mem T s i).mp hi).1

theorem signedSupportNegative_card (T : Finset Omega) (s : T → Bit) :
    (signedSupportNegative T s).card = hammingNorm s := by
  rw [signedSupportNegative,Finset.card_image_of_injective _ Subtype.val_injective]
  rfl

theorem signedSupportNegative_positive (T : Finset Omega) (s : T → Bit) (a : Omega)
    (ha : a ∈ T) (hz : s ⟨a,ha⟩ = 0) : a ∉ signedSupportNegative T s := by
  rw [signedSupportNegative_mem]
  simpa [hz]

theorem signedSupport_negative_formula (T : Finset Omega) (s : T → Bit) :
    signedSupport T s = fun i => constantSupportVector 1 T i-
      constantSupportVector 2 (signedSupportNegative T s) i := by
  funext i
  by_cases hi : i ∈ T
  · by_cases hz : s ⟨i,hi⟩ = 0
    · simp [signedSupport,constantSupportVector,hi,signedSupportNegative_mem,hz]
    · simp [signedSupport,constantSupportVector,hi,signedSupportNegative_mem,hz]
  · have hn : i ∉ signedSupportNegative T s := fun h => signedSupportNegative_subset T s h |> hi
    simp [signedSupport,constantSupportVector,hi,hn]

theorem permutation_signedSupport_of_sets (g : Mathieu24CodeModel) (S T : Finset Omega)
    (s : S → Bit) (t : T → Bit) (hT : permuteBlock g.val S = T)
    (hN : permuteBlock g.val (signedSupportNegative S s) = signedSupportNegative T t) :
    integerPermutation g.val (signedSupport S s) = signedSupport T t := by
  rw [signedSupport_negative_formula,signedSupport_negative_formula]
  change integerPermutation g.val (constantSupportVector 1 S-constantSupportVector 2 (signedSupportNegative S s)) = _
  rw [map_sub,permutation_constantSupport,permutation_constantSupport,hT,hN]
  rfl

end Atlas.Conway
