import Atlas.Fischer.ParkerSectionOctadRepresentatives
import Atlas.Fischer.CubicCanonicalTriangleTransport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Two actual loop elements with the same code differ by a central sign. -/
theorem parkerLoop_same_code_sign (x y : ParkerLoop) (h : x.1 = y.1) :
    ∃ e : Bit, x = parkerSign e y := by
  refine ⟨x.2+y.2,Prod.ext h ?_⟩
  change x.2 = y.2 + (x.2+y.2)
  have he : y.2+y.2 = 0 := CharTwo.add_self_eq_zero _
  calc
    _ = x.2 + (y.2+y.2) := by rw [he, add_zero]
    _ = _ := by abel

/-- Equivariance of chosen octad lifts forces a single product sign on every
actual tetrad-intersecting octad pair. -/
theorem parkerSection_uniform_octad_sign
    (s : Mathieu24CodeModel →* ParkerStandardGroup)
    (q : Octad → ParkerLoop) (hq : ∀ O, (q O).1 = octadWord O)
    (heq : ∀ g : Mathieu24CodeModel, ∀ O, q (g • O) = (s g).val (q O)) :
    ∃ e : Bit, ∀ D E F : Octad,
      octadWord F = octadWord D + octadWord E →
      parkerLoopMultiply (q D) (q E) = parkerSign e (q F) := by
  obtain ⟨e,he⟩ := parkerLoop_same_code_sign
    (parkerLoopMultiply (q countingCanonicalD) (q countingCanonicalSextetE))
    (q countingCanonicalSextetF) (by
      change (q countingCanonicalD).1 + (q countingCanonicalSextetE).1 = _
      rw [hq,hq,hq,countingCanonicalSextet_word])
  refine ⟨e,?_⟩
  intro D E F hF
  obtain ⟨g,hD,hE,hF⟩ := cubicSextetTriangle_canonical D E F hF
  apply (s g).val.injective
  rw [(s g).prop.1, ← heq g D, ← heq g E,
    parkerStandard_preserves_sign, ← heq g F, hD, hE, hF]
  exact he

end Atlas.Fischer
