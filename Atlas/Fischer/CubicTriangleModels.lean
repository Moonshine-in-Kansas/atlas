import Atlas.Fischer.CubicSliceOctadIncidence

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Actual ordered Golay octads forming a sextet triangle. -/
abbrev OrderedCubicSextetTriangle :=
  {t : Octad × Octad × Octad // octadWord t.2.2=octadWord t.1+octadWord t.2.1}

/-- Actual ordered Golay octads forming a trio. -/
abbrev OrderedCubicTrio :=
  {t : Octad × Octad × Octad // octadWord t.2.2=octadWord t.1+octadWord t.2.1+golayOne}

abbrev CubicOctadIntersectionRow (D : Octad) (k : ℕ) :=
  {E : Octad // (D.val ∩ E.val).card=k}

def cubicOctadIntersectionRowEquiv (D : Octad) (k : ℕ) :
    CubicOctadIntersectionRow D k ≃
      {E // E ∈ octads.filter (fun E => (D.val ∩ E).card=k)} where
  toFun E := ⟨E.val.val,Finset.mem_filter.mpr ⟨E.val.property,E.property⟩⟩
  invFun E := ⟨⟨E.val,(Finset.mem_filter.mp E.property).1⟩,(Finset.mem_filter.mp E.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cubicOctadIntersectionRow_card (D : Octad) (k : ℕ) :
    Nat.card (CubicOctadIntersectionRow D k)=octadIntersectionCount D.val ∅ k := by
  rw [Nat.card_congr (cubicOctadIntersectionRowEquiv D k),Nat.card_eq_fintype_card,Fintype.card_coe]
  unfold octadIntersectionCount
  congr 1
  ext E
  simp only [Finset.mem_filter,Finset.empty_subset,true_and,Finset.inter_comm]

def cubicSextetCompletion (D E : Octad) (h : (D.val ∩ E.val).card=4) : Octad :=
  signedOctadSupport (octadProductFour (canonicalOctadLift D) (canonicalOctadLift E)
    (by simpa only [signedOctadIntersection,signedOctadSupport_canonical] using h))

theorem cubicSextetCompletion_word (D E : Octad) (h : (D.val ∩ E.val).card=4) :
    octadWord (cubicSextetCompletion D E h)=octadWord D+octadWord E := by
  rw [cubicSextetCompletion,octadWord_signedSupport]
  rfl

def cubicTrioCompletion (D E : Octad) (h : (D.val ∩ E.val).card=0) : Octad :=
  signedOctadSupport (octadProductDisjoint (canonicalOctadLift D) (canonicalOctadLift E)
    (by simpa only [signedOctadIntersection,signedOctadSupport_canonical] using h))

theorem cubicTrioCompletion_word (D E : Octad) (h : (D.val ∩ E.val).card=0) :
    octadWord (cubicTrioCompletion D E h)=octadWord D+octadWord E+golayOne := by
  rw [cubicTrioCompletion,octadWord_signedSupport]
  rfl

end Atlas.Fischer
