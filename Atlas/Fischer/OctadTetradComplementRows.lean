import Atlas.Fischer.OctadTetradComplementTransport
import Atlas.Fischer.OctadTetradReflectionRows

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem rootMap_octadic_tetrad_second_row {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (E : OctadTetradFibre O T) :
    rootMap (octadicRoot Q 0) (signedOctadVector (octadTetradComplementLabel Q T hT D d hd E)) =
      (1 / 4 : Scalar) •
        ((∑ F : OctadTetradFibre O T, signedOctadVector (octadTetradComplementLabel Q T hT D d hd F)) -
          (2 : Scalar) • signedOctadVector (octadTetradComplementLabel Q T hT D d hd E)) +
      (theta / 4) •
        ((∑ F : OctadTetradFibre O T, signedOctadVector (octadTetradCosetLabel Q T D d hd F)) -
          (2 : Scalar) • signedOctadVector (octadTetradCosetLabel Q T D d hd E)) := by
  let e := octadTetradFlipEquiv O T hTO hT
  have h := rootMap_octadic_tetrad_first_row Q (O.val \ T)
    (octadTetrad_complement_card O T hTO hT) (e D) (parkerLoopMultiply d Q.octadLift.val)
    (octadTetradComplementBase_code Q T hTO hT D d hd) (e E)
  rw [octadTetradCosetLabel_flip, octadTetradComplementLabel_flip] at h
  rw [← e.sum_comp (fun F => signedOctadVector (octadTetradCosetLabel Q (O.val \ T)
      (e D) (parkerLoopMultiply d Q.octadLift.val)
      (octadTetradComplementBase_code Q T hTO hT D d hd) F)),
    ← e.sum_comp (fun F => signedOctadVector (octadTetradComplementLabel Q (O.val \ T)
      (octadTetrad_complement_card O T hTO hT) (e D) (parkerLoopMultiply d Q.octadLift.val)
      (octadTetradComplementBase_code Q T hTO hT D d hd) F))] at h
  have hy : (∑ F : OctadTetradFibre O T, signedOctadVector
      (octadTetradCosetLabel Q (O.val \ T) (e D) (parkerLoopMultiply d Q.octadLift.val)
        (octadTetradComplementBase_code Q T hTO hT D d hd) (e F))) =
      ∑ F : OctadTetradFibre O T, signedOctadVector (octadTetradComplementLabel Q T hT D d hd F) := by
    apply Finset.sum_congr rfl
    intro F hF
    exact congrArg signedOctadVector (octadTetradCosetLabel_flip Q T hTO hT D d hd F)
  have hz : (∑ F : OctadTetradFibre O T, signedOctadVector
      (octadTetradComplementLabel Q (O.val \ T) (octadTetrad_complement_card O T hTO hT)
        (e D) (parkerLoopMultiply d Q.octadLift.val)
        (octadTetradComplementBase_code Q T hTO hT D d hd) (e F))) =
      ∑ F : OctadTetradFibre O T, signedOctadVector (octadTetradCosetLabel Q T D d hd F) := by
    apply Finset.sum_congr rfl
    intro F hF
    exact congrArg signedOctadVector (octadTetradComplementLabel_flip Q T hTO hT D d hd F)
  rw [hy, hz] at h
  exact h


end Atlas.Fischer
