import Atlas.Fischer.GeneratedFrameMathieuImage
import Atlas.Fischer.GeneratedFrameNontrivial
import Atlas.Mathieu.Mathieu24Simplicity

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- An actual affine translation obtained from two octadic reflections makes
L0 nontrivial; no pre-existing Parker containment is used. -/
theorem generatedFrameMathieuImage_ne_bot : generatedFrameMathieuImage ≠ ⊥ := by
  obtain ⟨Ov,hOv⟩ := Finset.card_pos.mp (show 0 < octads.card by rw [octads_card]; decide)
  obtain ⟨e,he,hf,i,hi⟩ := rootGenerated_basicFrame_nontrivial ⟨Ov,hOv⟩
  exact generatedFrameMathieuImage_ne_bot_of_moved e he hf i hi

/-- The retained Mathieu simplicity theorem upgrades the actual normal
coordinate image of the generated frame stabilizer to all of M24. -/
theorem generatedFrameMathieuImage_eq_top : generatedFrameMathieuImage=⊤ := by
  letI : IsSimpleGroup Mathieu24CodeModel := Atlas.Codes.mathieu24_simple
  exact (generatedFrameMathieuImageNormal.eq_bot_or_eq_top).resolve_left
    generatedFrameMathieuImage_ne_bot

end Atlas.Fischer
