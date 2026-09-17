import Atlas.Fischer.MathieuOctadCharacters
import Atlas.Fischer.ParkerStandardParity
import Atlas.Fischer.ParkerSignNormalForm
import Atlas.Fischer.CubicTriangleAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The fixed-code normal form for a hypothetical group section, retaining
both actual code and actual loop coordinates. -/
theorem parkerSection_octad_form
    (s : Mathieu24CodeModel →* ParkerStandardGroup)
    (hs : parkerStandardProjection.comp s = MonoidHom.id _)
    (O : Octad) (g : MathieuOctadStabilizer O) (b : Bit) :
    (s g.val).val (octadWord O,b) =
      (octadWord O,b + ((s g.val).val (octadWord O,0)).2) := by
  have hp : parkerStandardProjection (s g.val) = g.val :=
    DFunLike.congr_fun hs g.val
  have hc : parkerCodeEquiv g.val (octadWord O) = octadWord O := by
    rw [← cubicTriangle_word_smul]
    exact congrArg octadWord g.prop
  have h := parkerPermutation_normal_form (s g.val).val (parkerCodeEquiv g.val)
    (s g.val).prop.1 (s g.val).prop.2.1
    (fun x => (parkerStandardProjection_spec (s g.val) x).trans (by rw [hp]))
    (octadWord O,b)
  simpa only [hc, parkerPermutationCorrection] using h

/-- The sign action of a hypothetical section on the two lifts of a fixed
actual octad is a binary character of its actual Mathieu stabilizer. -/
def parkerSection_octad_character
    (s : Mathieu24CodeModel →* ParkerStandardGroup)
    (hs : parkerStandardProjection.comp s = MonoidHom.id _)
    (O : Octad) : MathieuOctadStabilizer O →* Multiplicative Bit where
  toFun g := Multiplicative.ofAdd (((s g.val).val (octadWord O,0)).2)
  map_one' := by
    change Multiplicative.ofAdd (((s 1).val (octadWord O,0)).2) = 1
    rw [map_one]
    rfl
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    change ((s (g.val*h.val)).val (octadWord O,0)).2 =
      ((s g.val).val (octadWord O,0)).2 + ((s h.val).val (octadWord O,0)).2
    rw [map_mul]
    change ((s g.val).val ((s h.val).val (octadWord O,0))).2 = _
    rw [parkerSection_octad_form s hs O h 0]
    simp only [zero_add]
    rw [parkerSection_octad_form s hs O g]
    exact add_comm _ _

/-- A hypothetical M24 complement fixes both signed lifts of every octad
whenever its coordinate permutation stabilizes that octad. -/
theorem parkerSection_fixes_octad
    (s : Mathieu24CodeModel →* ParkerStandardGroup)
    (hs : parkerStandardProjection.comp s = MonoidHom.id _)
    (O : Octad) (g : Mathieu24CodeModel) (hg : g • O = O)
    (o : ParkerLoop) (ho : o.1 = octadWord O) : (s g).val o = o := by
  let k : MathieuOctadStabilizer O := ⟨g,hg⟩
  have ht := mathieuOctad_character_trivial O (parkerSection_octad_character s hs O) k
  have hz : ((s g).val (octadWord O,0)).2 = 0 :=
    congrArg Multiplicative.toAdd ht
  have he : o = (octadWord O,o.2) := Prod.ext ho rfl
  rw [he, parkerSection_octad_form s hs O k, hz, add_zero]

end Atlas.Fischer
