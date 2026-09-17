import Atlas.Fischer.OctadShortenedDivisibility
import Atlas.Fischer.ParkerCalibration
import Atlas.Fischer.ParkerTriplyEvenSubcodes

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes

/-- The actual shortened subcode, carrying its verified Parker identities. -/
noncomputable def octadElementarySubcode (O : Octad) : ParkerElementarySubcode :=
  .ofWeightDivisibility (octadShortenedCode O) (octadShortened_weight_dvd O)

/-- Every subcode of the actual shortened code has the same elementary-abelian
preimage property, with its retained inclusion into the Golay code. -/
noncomputable def octadElementarySubcodeOfLE (O : Octad) (K : Submodule Bit golay)
    (hK : K ≤ octadShortenedCode O) : ParkerElementarySubcode :=
  .ofWeightDivisibility K (fun a => octadShortened_weight_dvd O ⟨a.val,hK a.property⟩)

abbrev OctadParkerPreimage (O : Octad) := (octadElementarySubcode O).Preimage
abbrev OctadParkerSection (O : Octad) := ParkerSection (octadElementarySubcode O)

theorem octadShortenedCode_card (O : Octad) : Nat.card (octadShortenedCode O) = 32 := by
  letI : Fintype (octadShortenedCode O) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K := Bit),octadShortenedCode_finrank]
  norm_num [Bit,ZMod.card]

theorem octadParkerPreimage_card (O : Octad) : Nat.card (OctadParkerPreimage O) = 64 := by
  rw [ParkerElementarySubcode.preimage_card]
  change 2 * Nat.card (octadShortenedCode O) = 64
  rw [octadShortenedCode_card]

theorem octadParkerSection_card (O : Octad) : Nat.card (OctadParkerSection O) = 32 := by
  rw [ParkerSection.card]
  exact octadShortenedCode_card O

/-- Calibration is at the source element Ωo in the retained Parker loop. -/
theorem exists_octad_calibrated_section (O : Octad) (o : ParkerLoop)
    (ho : o.1 = octadWord O) :
    ∃ q : OctadParkerSection O,
      q.lift (octadShortenedOne O) = parkerLoopMultiply parkerOmega o := by
  apply ParkerSection.exists_omega_calibrated (K := octadElementarySubcode O) (octadShortenedOne O)
    (octadShortenedOne_ne_zero O) o
  change golayOne+octadWord O=golayOne+o.1
  rw [ho]

noncomputable def octadCalibratedSection (O : Octad) (o : ParkerLoop)
    (ho : o.1 = octadWord O) : OctadParkerSection O :=
  Classical.choose (exists_octad_calibrated_section O o ho)

theorem octadCalibratedSection_spec (O : Octad) (o : ParkerLoop)
    (ho : o.1 = octadWord O) :
    (octadCalibratedSection O o ho).lift (octadShortenedOne O) =
      parkerLoopMultiply parkerOmega o :=
  Classical.choose_spec (exists_octad_calibrated_section O o ho)

theorem octadCalibratedSection_card (O : Octad) (o : ParkerLoop)
    (ho : o.1 = octadWord O) :
    Nat.card (ParkerSection.LiftCalibrated (K := octadElementarySubcode O)
      (octadShortenedOne O) (parkerLoopMultiply parkerOmega o)) = 16 := by
  rw [ParkerSection.lift_calibrated_card (K := octadElementarySubcode O) _ (octadShortenedOne_ne_zero O) _ (by
    change golayOne+o.1=golayOne+octadWord O
    rw [ho])]
  change Nat.card (octadShortenedCode O) / 2 = 16
  rw [octadShortenedCode_card]

end Atlas.Fischer
