import Atlas.Fischer.GolayCoordinateVectors
import Atlas.Fischer.DuadCoordinateFormulaTransport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The actual octad coordinate underlying an eight- or sixteen-word. -/
def duadWordOctad (p : Finset Omega) (c : DuadCoordinateWord p) : Octad :=
  if h8 : hammingNorm c.val.val.val=8 then golayOctadOfWeight c.val.val h8
  else golayOctadOfWeight (c.val.val+golayOne)
    (golayComplement_weight_sixteen _ (c.property.resolve_left h8))

/-- Its Golay label retains whether complementation was required. -/
theorem duadWordOctad_word (p : Finset Omega) (c : DuadCoordinateWord p) :
    octadWord (duadWordOctad p c)=c.val.val +
      if hammingNorm c.val.val.val=8 then 0 else golayOne := by
  unfold duadWordOctad
  split_ifs <;> rw [golayOctadOfWeight_word] <;> simp

/-- Shortening on a nonempty duad excludes complementary duplicate labels. -/
theorem duadWordOctad_injective (p : Finset Omega) (hp : p.Nonempty) :
    Function.Injective (duadWordOctad p) := by
  intro c d h
  have hw := congrArg octadWord h
  rw [duadWordOctad_word,duadWordOctad_word] at hw
  have he : (hammingNorm c.val.val.val=8) ↔ (hammingNorm d.val.val.val=8) := by
    obtain ⟨i,hi⟩ := hp
    have hz := congrArg (fun w : golay => w.val i) hw
    have hc := (mem_duadShortenedCode p c.val.val).mp c.val.property i hi
    have hd := (mem_duadShortenedCode p d.val.val).mp d.val.property i hi
    by_cases h8c : hammingNorm c.val.val.val=8 <;>
      by_cases h8d : hammingNorm d.val.val.val=8
    · exact iff_of_true h8c h8d
    · simp only [h8c,h8d,ite_true,ite_false,add_zero] at hz
      change c.val.val.val i = d.val.val.val i + 1 at hz
      rw [hc,hd,zero_add] at hz
      exact False.elim (zero_ne_one hz)
    · simp only [h8c,h8d,ite_true,ite_false,add_zero] at hz
      change c.val.val.val i + 1 = d.val.val.val i at hz
      rw [hc,hd,zero_add] at hz
      exact False.elim (one_ne_zero hz)
    · exact iff_of_false h8c h8d
  have hcd : c.val.val=d.val.val := by
    by_cases hc : hammingNorm c.val.val.val=8
    · simpa only [hc,he.mp hc,ite_true,add_zero] using hw
    · have hd : ¬hammingNorm d.val.val.val=8 := fun h => hc (he.mpr h)
      simp only [hc,hd,ite_false] at hw
      exact add_right_cancel hw
  exact Subtype.ext (Subtype.ext hcd)

/-- The scalar coefficient includes the retained Parker sign in weight sixteen. -/
def duadWordScalar (p : Finset Omega) (c : DuadCoordinateWord p) : Scalar :=
  if hammingNorm c.val.val.val=8 then 1 else
    theta * parkerScalarSign (parkerLoopMultiply (c.val.val,0) parkerOmega).2

/-- Each word vector is literally one nonzero octad coordinate. -/
theorem duadWordVector_octad (p : Finset Omega) (c : DuadCoordinateWord p) :
    duadWordVector p c=duadWordScalar p c • xOctad (duadWordOctad p c) := by
  unfold duadWordVector golayCoordinateVector duadWordScalar duadWordOctad
  split_ifs with h8
  · simp only [signedOctadVector,parkerScalarSign,ite_true,one_smul]
    rfl
  · rw [signedOctadVector,smul_smul]
    rfl

theorem duadWordScalar_ne_zero (p : Finset Omega) (c : DuadCoordinateWord p) :
    duadWordScalar p c ≠ 0 := by
  unfold duadWordScalar
  split_ifs
  · exact one_ne_zero
  · exact mul_ne_zero theta_ne_zero (parkerScalarSign_ne_zero _)

end Atlas.Fischer
