import Atlas.Fischer.OctadTetradPairedLabels
import Atlas.Fischer.OctadScalarBlockGeometry
import Atlas.Fischer.SignedCoordinateIndependence

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def octadTetradPairedLabel {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val)
    (p : OctadTetradFibre O T × Fin 2) : SignedOctad :=
  if p.2 = 0 then octadTetradCosetLabel Q T D d hd p.1
  else octadTetradComplementLabel Q T hT D d hd p.1

theorem octadTetradPairedFamily_eq {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val)
    (p : OctadTetradFibre O T × Fin 2) :
    octadTetradPairedFamily Q T hT D d hd p =
      signedOctadVector (octadTetradPairedLabel Q T hT D d hd p) := by
  simp only [octadTetradPairedFamily,octadTetradPairedLabel]
  split <;> rfl

theorem octadTetradPairedLabel_support_injective {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4)
    (D : OctadTetradFibre O T) (d : ParkerLoop) (hd : d.1 = octadWord D.val) :
    Function.Injective (fun p => signedOctadSupport (octadTetradPairedLabel Q T hT D d hd p)) := by
  have hne : T ≠ O.val \ T := by
    intro h
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
    have := Finset.mem_sdiff.mp (h ▸ hi)
    exact this.2 hi
  have hcross (E F : OctadTetradFibre O T) : E.val ≠ octadTetradFlip O T hT F := by
    intro h
    have he := congrArg (fun A : Octad => A.val ∩ O.val) h
    rw [E.property,octadTetradFlip_restriction] at he
    exact hne he
  rintro ⟨E,i⟩ ⟨F,j⟩ h
  fin_cases i <;> fin_cases j <;>
    simp [octadTetradPairedLabel,octadTetradCosetLabel_support,
      octadTetradComplementLabel_support] at h
  · exact Prod.ext (Subtype.ext h) rfl
  · exact (hcross E F h).elim
  · exact (hcross F E h.symm).elim
  · have he : (octadTetradFlipEquiv O T hTO hT) E =
        (octadTetradFlipEquiv O T hTO hT) F := Subtype.ext h
    exact Prod.ext ((octadTetradFlipEquiv O T hTO hT).injective he) rfl

theorem octadTetradPairedFamily_independent {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4)
    (D : OctadTetradFibre O T) (d : ParkerLoop) (hd : d.1 = octadWord D.val) :
    LinearIndependent Scalar (octadTetradPairedFamily Q T hT D d hd) := by
  have hj := octadTetradPairedLabel_support_injective Q T hTO hT D d hd
  have h := signedCoordinate_linearIndependent
    (fun p => Sum.inr (signedOctadSupport (octadTetradPairedLabel Q T hT D d hd p)))
    (fun _ _ he => hj (Sum.inr.inj he))
    (fun p => (octadTetradPairedLabel Q T hT D d hd p).val.2)
  convert h using 1
  funext p
  exact octadTetradPairedFamily_eq Q T hT D d hd p

theorem octadTetradPairedFamily_mem {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4)
    (D : OctadTetradFibre O T) (d : ParkerLoop) (hd : d.1 = octadWord D.val)
    (p : OctadTetradFibre O T × Fin 2) :
    octadTetradPairedFamily Q T hT D d hd p ∈ octadScalarBlock O T := by
  rcases p with ⟨E,i⟩
  fin_cases i
  · simp only [octadTetradPairedFamily,↓reduceIte]
    apply Submodule.smul_mem
    apply coordinateVector_mem_octadScalarBlock
    refine ⟨0,?_⟩
    change (signedOctadSupport (octadTetradCosetLabel Q T D d hd E)).val ∩ O.val = T
    rw [octadTetradCosetLabel_support,E.property]
  · simp only [octadTetradPairedFamily,↓reduceIte]
    apply Submodule.smul_mem
    apply coordinateVector_mem_octadScalarBlock
    refine ⟨1,?_⟩
    rw [octadRationalLabel_one_eq_complement]
    change O.val \ ((signedOctadSupport (octadTetradComplementLabel Q T hT D d hd E)).val ∩ O.val) = T
    rw [octadTetradComplementLabel_support,octadTetradFlip_restriction,
      Finset.sdiff_sdiff_eq_self hTO]

/-- The eight actual Parker-labelled vectors span the intended tetrad block. -/
theorem octadTetradPairedFamily_span {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4)
    (D : OctadTetradFibre O T) (d : ParkerLoop) (hd : d.1 = octadWord D.val) :
    Submodule.span Scalar (Set.range (octadTetradPairedFamily Q T hT D d hd)) =
      octadScalarBlock O T := by
  apply Submodule.eq_of_le_of_finrank_le
  · apply Submodule.span_le.mpr
    rintro x ⟨p,rfl⟩
    exact octadTetradPairedFamily_mem Q T hTO hT D d hd p
  · rw [finrank_span_eq_card (octadTetradPairedFamily_independent Q T hTO hT D d hd),
      octadScalarBlock_tetrad_dimension O T hTO hT]
    rw [← Nat.card_eq_fintype_card, Nat.card_prod,octadTetradFibre_card O T hTO hT]
    simp

end Atlas.Fischer
