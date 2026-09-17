import Atlas.Fischer.CountingColumnRule

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Simultaneous row translation preserves each actual column intersection count. -/
theorem countingSourceColumn_translation_inter_card (b : countingHexacode)
    (t u : CountingSourceParameters) (i : Fin 6) :
    (countingSourceColumn (countingSourceTranslation b t) i ∩
      countingSourceColumn (countingSourceTranslation b u) i).card=
      (countingSourceColumn t i ∩ countingSourceColumn u i).card := by
  apply Finset.card_bij (fun z _ => z+b.val i)
  · intro z hz
    obtain ⟨ht,hu⟩ := Finset.mem_inter.mp hz
    exact Finset.mem_inter.mpr
      ⟨(countingSourceColumn_translation b t i z).mpr ht,
       (countingSourceColumn_translation b u i z).mpr hu⟩
  · intro z _ w _ he
    exact add_right_cancel he
  · intro z hz
    refine ⟨z-b.val i,?_,sub_add_cancel z (b.val i)⟩
    obtain ⟨ht,hu⟩ := Finset.mem_inter.mp hz
    apply Finset.mem_inter.mpr
    constructor
    · apply (countingSourceColumn_translation b t i (z-b.val i)).mp
      simpa only [sub_add_cancel] using ht
    · apply (countingSourceColumn_translation b u i (z-b.val i)).mp
      simpa only [sub_add_cancel] using hu

theorem countingSourceColumn_translation_card (b : countingHexacode)
    (t : CountingSourceParameters) (i : Fin 6) :
    (countingSourceColumn (countingSourceTranslation b t) i).card=(countingSourceColumn t i).card := by
  simpa only [Finset.inter_self] using countingSourceColumn_translation_inter_card b t t i

/-- The column-rule weight evaluated on actual source parameters. -/
def countingSourceWeight (epsilon : ℕ) (D E F : Finset (Fin 6))
    (t u : CountingSourceParameters) : Option ℤ :=
  countingColumnWeight epsilon D E F
    (fun i => (countingSourceColumn t i).card)
    (fun i => (countingSourceColumn u i).card)
    (fun i => (countingSourceColumn t i ∩ countingSourceColumn u i).card)

/-- The full signed column weight is unchanged by every actual codeword translation. -/
theorem countingSourceWeight_translation (epsilon : ℕ) (D E F : Finset (Fin 6))
    (b : countingHexacode) (t u : CountingSourceParameters) :
    countingSourceWeight epsilon D E F (countingSourceTranslation b t) (countingSourceTranslation b u)=
      countingSourceWeight epsilon D E F t u := by
  simp only [countingSourceWeight,countingSourceColumn_translation_card,
    countingSourceColumn_translation_inter_card]

end Atlas.Fischer
