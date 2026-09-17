import Atlas.Fischer.OctadicRootTransport
import Atlas.Mathieu.GolayOctadTransitivity

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem parkerOctadAction_transitive (O P : Octad) :
    ∃ e : ParkerStandardGroup, parkerOctadAction e O = P := by
  obtain ⟨g, hg⟩ := mathieu24_octad_transitive O.val P.val O.property P.property
  obtain ⟨e, he⟩ := parkerStandardProjection_surjective g
  refine ⟨e, ?_⟩
  apply Subtype.ext
  change permuteBlock (parkerStandardProjection e).val O.val = P.val
  rw [he]
  exact hg

/-- Transitivity on all displayed octadic vectors follows from actual M24 octad
transitivity, actual Parker lifts, and actual cocode phase transport. -/
theorem octadicRoot_H_transitive {O P : Octad} (Q : OctadCalibration O)
    (R : OctadCalibration P) (χ : OctadicCharacter O) (ψ : OctadicCharacter P) :
    ∃ e : ParkerStandardGroup, parkerCoordinateAction e (octadicRoot Q χ) = octadicRoot R ψ := by
  obtain ⟨e, he⟩ := parkerOctadAction_transitive O P
  subst P
  let χe := (octadCharacterPullback e O).symm χ
  have hx : parkerCoordinateAction e (octadicRoot Q χ) =
      octadicRoot R (χe + octadCalibrationDifference R (octadCalibrationTransport e Q)) := by
    rw [parkerCoordinateAction_octadicRoot,
      octadicRoot_change R (octadCalibrationTransport e Q)]
  obtain ⟨d, hd⟩ := octadicRoot_cocode_transitive R
    (χe + octadCalibrationDifference R (octadCalibrationTransport e Q)) ψ
  refine ⟨parkerCocodeStandard d * e, ?_⟩
  rw [parkerCoordinateAction_mul, hx, hd]

end Atlas.Fischer
