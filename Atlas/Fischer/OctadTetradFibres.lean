import Atlas.Fischer.OctadPunctureFibres
import Atlas.Fischer.OctadicCrossingExpansion
import Atlas.Fischer.OctadScalarBlocks

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

abbrev OctadTetradFibre (O : Octad) (T : Finset Omega) := {D : Octad // D.val ∩ O.val = T}

def octadTetradFibreFilterEquiv (O : Octad) (T : Finset Omega) :
    OctadTetradFibre O T ≃ {D // D ∈ octads.filter (fun D => D ∩ O.val = T)} where
  toFun D := ⟨D.val.val, Finset.mem_filter.mpr ⟨D.val.property, D.property⟩⟩
  invFun D := ⟨⟨D.val, (Finset.mem_filter.mp D.property).1⟩, (Finset.mem_filter.mp D.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem octadTetradFibre_card (O : Octad) (T : Finset Omega)
    (hTO : T ⊆ O.val) (hT : T.card = 4) : Nat.card (OctadTetradFibre O T) = 4 := by
  rw [Nat.card_congr (octadTetradFibreFilterEquiv O T), Nat.card_eq_fintype_card, Fintype.card_coe]
  exact octadRestrictionCount_tetrad O.val T O.property hTO hT

/-- Complementation of the interior tetrad is the actual Golay sum D+O. -/
def octadTetradFlip (O : Octad) (T : Finset Omega) (hT : T.card = 4)
    (D : OctadTetradFibre O T) : Octad :=
  signedOctadSupport (octadProductFour (canonicalOctadLift D.val) (canonicalOctadLift O) (by
    rw [signedOctadIntersection, signedOctadSupport_canonical, signedOctadSupport_canonical,
      D.property, hT]))

theorem octadTetradFlip_word (O : Octad) (T : Finset Omega) (hT : T.card = 4)
    (D : OctadTetradFibre O T) :
    octadWord (octadTetradFlip O T hT D) = octadWord D.val + octadWord O := by
  rw [octadTetradFlip, octadWord_signedSupport]
  rfl

theorem octadTetradFlip_restriction (O : Octad) (T : Finset Omega) (hT : T.card = 4)
    (D : OctadTetradFibre O T) : (octadTetradFlip O T hT D).val ∩ O.val = O.val \ T := by
  rw [← octadWord_support (octadTetradFlip O T hT D), octadTetradFlip_word]
  conv_rhs => rw [← D.property]
  ext i
  by_cases ho : i ∈ O.val <;> by_cases hd : i ∈ D.val.val <;>
    simp [support, octadWord_apply, ho, hd]

theorem octadTetradFlip_exterior (O : Octad) (T : Finset Omega) (hT : T.card = 4)
    (D : OctadTetradFibre O T) :
    octadExteriorWord O (octadWord (octadTetradFlip O T hT D)) =
      octadExteriorWord O (octadWord D.val) := by
  rw [octadTetradFlip_word, map_add]
  have hz : octadExteriorWord O (octadWord O) = 0 := by
    apply (octadExteriorWord_eq_zero_iff O _).mpr
    intro i hi
    simp only [octadWord_apply, ite_eq_right hi]
  rw [hz, add_zero]

theorem octadTetradFibre_exterior_weight (O : Octad) (T : Finset Omega) (hT : T.card = 4)
    (D : OctadTetradFibre O T) : hammingNorm (octadExteriorWord O (octadWord D.val)) = 4 := by
  have h := octadExteriorWord_weight_in_restriction O D.val T D.property
  omega


theorem octadTetrad_complement_card (O : Octad) (T : Finset Omega)
    (hTO : T ⊆ O.val) (hT : T.card = 4) : (O.val \ T).card = 4 := by
  rw [Finset.card_sdiff_of_subset hTO, octad_size O.val O.property, hT]

def octadTetradFlipEquiv (O : Octad) (T : Finset Omega)
    (hTO : T ⊆ O.val) (hT : T.card = 4) :
    OctadTetradFibre O T ≃ OctadTetradFibre O (O.val \ T) where
  toFun D := ⟨octadTetradFlip O T hT D, octadTetradFlip_restriction O T hT D⟩
  invFun E := ⟨octadTetradFlip O (O.val \ T) (octadTetrad_complement_card O T hTO hT) E, by
    rw [octadTetradFlip_restriction, Finset.sdiff_sdiff_eq_self hTO]⟩
  left_inv D := by
    apply octadExteriorWord_injective_on_restriction O T
    simp only [octadTetradFlip_exterior]
  right_inv E := by
    apply octadExteriorWord_injective_on_restriction O (O.val \ T)
    simp only [octadTetradFlip_exterior]

end Atlas.Fischer

