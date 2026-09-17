import Atlas.Fischer.OctadTetradCosetLabels

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem octadTetradCosetLabel_intersection {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (E : OctadTetradFibre O T) :
    signedOctadIntersection (octadTetradCosetLabel Q T D d hd E) Q.octadLift = 4 := by
  have ho : signedOctadSupport Q.octadLift = O :=
    (signedOctadSupport_eq_iff _ _).mpr Q.lift_code
  rw [signedOctadIntersection, octadTetradCosetLabel_support, ho, E.property, hT]

/-- Complementary basis vectors retain the actual Parker product with the marked lift o. -/
def octadTetradComplementLabel {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (E : OctadTetradFibre O T) : SignedOctad :=
  octadProductFour (octadTetradCosetLabel Q T D d hd E) Q.octadLift
    (octadTetradCosetLabel_intersection Q T hT D d hd E)

theorem octadTetradComplementLabel_code {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (E : OctadTetradFibre O T) :
    (octadTetradComplementLabel Q T hT D d hd E).val.1 = octadWord E.val + octadWord O := by
  change (octadTetradCosetLabel Q T D d hd E).val.1 + Q.octadLift.val.1 = _
  rw [octadTetradCosetLabel_code, Q.lift_code]

theorem octadTetradComplementLabel_support {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (E : OctadTetradFibre O T) :
    signedOctadSupport (octadTetradComplementLabel Q T hT D d hd E) = octadTetradFlip O T hT E := by
  apply (signedOctadSupport_eq_iff _ _).mpr
  rw [octadTetradComplementLabel_code, octadTetradFlip_word]

/-- Actual four-by-two signed coordinate family; no independent sign gauge is inserted. -/
def octadTetradPairedFamily {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) :
    OctadTetradFibre O T × Fin 2 → Coordinates := fun p =>
  if p.2 = 0 then signedOctadVector (octadTetradCosetLabel Q T D d hd p.1)
  else signedOctadVector (octadTetradComplementLabel Q T hT D d hd p.1)

end Atlas.Fischer
