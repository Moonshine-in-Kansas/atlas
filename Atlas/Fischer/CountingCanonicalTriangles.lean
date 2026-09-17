import Atlas.Fischer.CountingCanonicalOctads

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

 theorem countingColumnPairOctad_word_apply (i j : Fin 6) (hij : i ≠ j) (p : Omega) :
    (octadWord (countingColumnPairOctad i j hij)).val p =
      if hexIndexEquiv p.1 = i ∨ hexIndexEquiv p.1 = j then 1 else 0 := by
  rw [octadWord_apply]
  have hm : p ∈ (countingColumnPairOctad i j hij).val ↔
      hexIndexEquiv p.1 = i ∨ hexIndexEquiv p.1 = j := by
    rw [countingColumnPairOctad,countingSourceColumn_membership]
    change _ ∈ (if hexIndexEquiv p.1 ∈ ({i,j} : Finset (Fin 6)) then Finset.univ else ∅) ↔ _
    by_cases h : hexIndexEquiv p.1 = i ∨ hexIndexEquiv p.1 = j <;> simp [h]
  simp only [hm]

 theorem countingCanonicalSextet_word :
    octadWord countingCanonicalSextetF = octadWord countingCanonicalD + octadWord countingCanonicalSextetE := by
  apply Subtype.ext
  funext p
  simp only [Submodule.coe_add,Pi.add_apply,countingCanonicalSextetF,countingCanonicalD,
    countingCanonicalSextetE,countingColumnPairOctad_word_apply]
  have h : ∀ a : Fin 6, (if a = 1 ∨ a = 2 then (1 : Bit) else 0) =
      (if a = 0 ∨ a = 1 then 1 else 0) + (if a = 0 ∨ a = 2 then 1 else 0) := by decide
  exact h (hexIndexEquiv p.1)

 theorem countingCanonicalTrio_word :
    octadWord countingCanonicalTrioF = octadWord countingCanonicalD + octadWord countingCanonicalTrioE + golayOne := by
  apply Subtype.ext
  funext p
  simp only [Submodule.coe_add,Pi.add_apply,countingCanonicalTrioF,countingCanonicalD,
    countingCanonicalTrioE,countingColumnPairOctad_word_apply,golayOne,allOnes]
  have h : ∀ a : Fin 6, (if a = 4 ∨ a = 5 then (1 : Bit) else 0) =
      (if a = 0 ∨ a = 1 then 1 else 0) + (if a = 2 ∨ a = 3 then 1 else 0) + 1 := by decide
  exact h (hexIndexEquiv p.1)

end Atlas.Fischer
