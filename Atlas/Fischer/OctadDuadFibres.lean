import Atlas.Fischer.OctadQuadraticTranslations

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
attribute [local instance] Classical.propDecidable

theorem octadVectorTranslation_inside (O : Octad) (t : BinaryFour) (i : Omega)
    (hi : i ∈ O.val) : (octadVectorTranslation O t).val.val i=i := by
  have h := mathieuOctadCharacterLift_mem O ((octadDirectionCoordinates O).symm t)
  change mathieuOctadAlternatingHom O (octadVectorTranslation O t)=1 at h
  have he := congrArg (fun g : alternatingGroup (OctadInterior O) => g.val ⟨i,hi⟩) h
  exact congrArg Subtype.val he

theorem octadTranslatedWord_inside (O : Octad) (t : BinaryFour) (c : golay) :
    octadEvenRestriction O (octadTranslatedWord O t c)=octadEvenRestriction O c := by
  apply Subtype.ext
  funext i
  change c.val ((octadVectorTranslation O t).val.val i.val)=c.val i.val
  rw [octadVectorTranslation_inside O t i.val i.property]

/-- The translated octad is obtained from an actual Mathieu-translated Golay word. -/
def octadTranslatedOctad (O D : Octad) (t : BinaryFour) : Octad :=
  ⟨support (octadTranslatedWord O t (octadWord D)).val,
    (octads_mem _).mpr ⟨octadTranslatedWord O t (octadWord D),
      (octadTranslatedWord_weight O t (octadWord D)).trans (octadWord_weight D),rfl⟩⟩

theorem octadTranslatedOctad_word (O D : Octad) (t : BinaryFour) :
    octadWord (octadTranslatedOctad O D t)=octadTranslatedWord O t (octadWord D) := by
  apply Subtype.ext
  apply support_injective
  exact octadWord_support _

theorem octadTranslatedOctad_intersection (O D : Octad) (t : BinaryFour) :
    (octadTranslatedOctad O D t).val ∩ O.val=D.val ∩ O.val := by
  ext i
  by_cases hi : i ∈ O.val
  · simp only [Finset.mem_inter,hi,and_true]
    change i ∈ support (octadTranslatedWord O t (octadWord D)).val ↔ i ∈ D.val
    simp only [support,Finset.mem_filter,Finset.mem_univ,true_and]
    change ((octadWord D).val ((octadVectorTranslation O t).val.val i) ≠ 0) ↔ i ∈ D.val
    rw [octadVectorTranslation_inside O t i hi]
    simp only [octadWord_apply]
    split_ifs <;> simp_all
  · simp only [Finset.mem_inter,hi,and_false]

abbrev OctadDuadFibre (O : Octad) (S : Finset Omega) :=
  {D : Octad // D.val ∩ O.val=S}

def octadDuadTranslation (O : Octad) (S : Finset Omega) (D : OctadDuadFibre O S)
    (t : BinaryFour) : OctadDuadFibre O S :=
  ⟨octadTranslatedOctad O D.val t,(octadTranslatedOctad_intersection O D.val t).trans D.property⟩

theorem octadDuadTranslation_injective (O : Octad) (S : Finset Omega)
    (D : OctadDuadFibre O S) (hS : S.card=2) :
    Function.Injective (octadDuadTranslation O S D) := by
  intro s t h
  apply octadTranslatedWord_duad_injective O (octadWord D.val)
    (by rw [octadWord_support,D.property,hS])
  have he := congrArg (fun E : OctadDuadFibre O S => octadWord E.val) h
  simpa only [octadDuadTranslation,octadTranslatedOctad_word] using he

def octadDuadFibreFilterEquiv (O : Octad) (S : Finset Omega) :
    OctadDuadFibre O S ≃ {D // D ∈ octads.filter (fun D => D ∩ O.val=S)} where
  toFun D := ⟨D.val.val,Finset.mem_filter.mpr ⟨D.val.property,D.property⟩⟩
  invFun D := ⟨⟨D.val,(Finset.mem_filter.mp D.property).1⟩,(Finset.mem_filter.mp D.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem octadDuadFibre_card (O : Octad) (S : Finset Omega) (hSO : S ⊆ O.val)
    (hS : S.card=2) : Nat.card (OctadDuadFibre O S)=16 := by
  rw [Nat.card_congr (octadDuadFibreFilterEquiv O S),Nat.card_eq_fintype_card,Fintype.card_coe]
  exact octadRestrictionCount_duad O.val S O.property hSO hS

/-- Sixteen actual translations label the entire actual duad fibre bijectively. -/
def octadDuadTranslationEquiv (O : Octad) (S : Finset Omega) (D : OctadDuadFibre O S)
    (hS : S.card=2) : BinaryFour ≃ OctadDuadFibre O S :=
  Equiv.ofBijective (octadDuadTranslation O S D)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨octadDuadTranslation_injective O S D hS,by
        rw [octadDuadFibre_card O S (D.property ▸ Finset.inter_subset_right) hS]
        change Nat.card (Fin 4 → Bit)=16
        simp [Nat.card_fun,Bit,ZMod.card]⟩)

end Atlas.Fischer
