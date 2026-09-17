import Atlas.Fischer.CountingSourceTranslations

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

abbrev CountingSourceParameters := CountingSourceTypeA ⊕ (CountingSourceTypeB ⊕ CountingSourceTypeC)

/-- Literal column subsets of each source parameter, in the verified F4 row labels. -/
def countingSourceColumn : CountingSourceParameters → Fin 6 → Finset CountingFour
  | .inl t,i => if i ∈ t.val then Finset.univ else ∅
  | .inr (.inl t),i => countingColumnPair (t.1.val.val i) (t.2.val.val i)
  | .inr (.inr t),i => countingColumnSingleton (t.1.val i) (decide (i=t.2))

theorem countingSourceColumn_card_A (t : CountingSourceTypeA) (i : Fin 6) :
    (countingSourceColumn (.inl t) i).card=if i ∈ t.val then 4 else 0 := by
  by_cases hi : i ∈ t.val <;> simp [countingSourceColumn,hi,Atlas.Algebra.goldenFour_card]

theorem countingSourceColumn_card_B (t : CountingSourceTypeB) (i : Fin 6) :
    (countingSourceColumn (.inr (.inl t)) i).card=if t.1.val.val i=0 then 0 else 2 := by
  have h : ∀ (g : CountingFour) (e : Bit),
      (countingColumnPair g e).card=if g=0 then 0 else 2 := by decide
  exact h _ _

theorem countingSourceColumn_card_C (t : CountingSourceTypeC) (i : Fin 6) :
    (countingSourceColumn (.inr (.inr t)) i).card=if i=t.2 then 3 else 1 := by
  have h : ∀ (g : CountingFour) (d : Bool),
      (countingColumnSingleton g d).card=if d then 3 else 1 := by decide
  change (countingColumnSingleton (t.1.val i) (decide (i=t.2))).card = _
  simpa using h (t.1.val i) (decide (i=t.2))

/-- The source column subsets describe the actual retained octad, point for point. -/
theorem countingSourceColumn_membership (t : CountingSourceParameters) (p : Omega) :
    p ∈ (countingSourceOctadEquiv t).val ↔
      (countingPointCoordinates p).2 ∈ countingSourceColumn t (countingPointCoordinates p).1 := by
  rcases t with a | (b | c)
  · obtain ⟨a,rfl⟩ := countingTypeA_sourceEquiv.surjective a
    have he : countingSourceOctadEquiv (.inl (countingTypeA_sourceEquiv a))=countingOctad (.inl a) := by
      change countingOctad (.inl (countingTypeA_sourceEquiv.symm (countingTypeA_sourceEquiv a)))=_
      rw [Equiv.symm_apply_apply]
    rw [he,countingTypeA_membership]
    by_cases hi : (countingPointCoordinates p).1 ∈ support a.val.val <;>
      simp [countingSourceColumn,countingTypeA_sourceEquiv,countingTypeA_source,hi]
  · obtain ⟨b,rfl⟩ := countingTypeB_sourceEquiv.surjective b
    have he : countingSourceOctadEquiv (.inr (.inl (countingTypeB_sourceEquiv b)))=countingOctad (.inr (.inl b)) := by
      change countingOctad (.inr (.inl (countingTypeB_sourceEquiv.symm (countingTypeB_sourceEquiv b))))=_
      rw [Equiv.symm_apply_apply]
    rw [he,countingTypeB_membership]
    change _ ↔ _ ∈ countingColumnPair
      (countingHexCoordinates b.1.val.val (countingPointCoordinates p).1)
      (countingPairMask b.1.val b.2.val (countingPointCoordinates p).1)
    simp only [countingColumnPair]
    split_ifs <;> simp_all
  · obtain ⟨c,rfl⟩ := countingTypeC_sourceEquiv.surjective c
    have he : countingSourceOctadEquiv (.inr (.inr (countingTypeC_sourceEquiv c)))=countingOctad (.inr (.inr c)) := by
      change countingOctad (.inr (.inr (countingTypeC_sourceEquiv.symm (countingTypeC_sourceEquiv c))))=_
      rw [Equiv.symm_apply_apply]
    rw [he,countingTypeC_membership]
    change _ ↔ _ ∈ countingColumnSingleton
      (countingHexCoordinates c.1.val (countingPointCoordinates p).1)
      (decide ((countingPointCoordinates p).1=countingDistinguishedColumn c))
    simp only [countingColumnSingleton]
    split_ifs <;> simp_all

/-- Codeword translation permutes all three parameter types without changing columns. -/
def countingSourceTranslation (b : countingHexacode) : CountingSourceParameters ≃ CountingSourceParameters :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (countingSourceBTranslation b)
    (countingSourceCTranslation b))

theorem countingSourceColumn_translation (b : countingHexacode) (t : CountingSourceParameters)
    (i : Fin 6) (z : CountingFour) :
    z+b.val i ∈ countingSourceColumn t i ↔
      z ∈ countingSourceColumn (countingSourceTranslation b t) i := by
  rcases t with a | (g | h)
  · by_cases hi : i ∈ a.val <;> simp [countingSourceColumn,countingSourceTranslation,hi]
  · exact countingColumnPair_translation _ _ _ _
  · exact countingColumnSingleton_translation _ _ _ _

end Atlas.Fischer
