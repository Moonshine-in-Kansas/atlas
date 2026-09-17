import Atlas.Fischer.CountingColumnIntersections
import Atlas.Fischer.OctadShortenedCode
import Atlas.Combinatorics.FiniteSymmetricDifferenceCard

noncomputable section
namespace Atlas.Fischer
open scoped symmDiff
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The actual Golay diamond is symmetric difference, complemented in the disjoint case. -/
theorem octadDiamond_support (G H : Octad) (h : OctadPairAdmissible G H) :
    (octadDiamond G H h).val=
      if (G.val ∩ H.val).card=0 then (G.val ∆ H.val)ᶜ else G.val ∆ H.val := by
  ext p
  have he := congrArg (fun w : golay => w.val p) (octadDiamond_word G H h)
  by_cases h0 : (G.val ∩ H.val).card=0 <;>
    by_cases hG : p ∈ G.val <;> by_cases hH : p ∈ H.val <;>
      by_cases hJ : p ∈ (octadDiamond G H h).val <;>
        simp [octadWord_apply,h0,hG,hH,hJ,golayOne,allOnes,Finset.mem_symmDiff] at he ⊢

/-- The source formula for every column of the actual diamond. -/
theorem countingColumnProfile_diamond (G H : Octad) (h : OctadPairAdmissible G H) :
    countingColumnProfile (octadDiamond G H h).val=
      countingDiamondColumns (octadDelta G H) (countingColumnProfile G.val)
        (countingColumnProfile H.val) (countingColumnJointProfile G.val H.val) := by
  funext i
  rw [octadDiamond_support]
  by_cases h0 : (G.val ∩ H.val).card=0
  · simp only [h0,ite_true,countingColumnProfile,countingPointColumn_compl_card,
      countingPointColumn_symmDiff,Atlas.Combinatorics.card_symmDiff_eq,
      countingDiamondColumns,octadDelta,show (1 : ℕ) ≠ 0 by decide,ite_false,
      countingColumnJointProfile]
  · simp only [h0,ite_false,countingColumnProfile,countingPointColumn_symmDiff,
      Atlas.Combinatorics.card_symmDiff_eq,countingDiamondColumns,octadDelta,
      ite_true,countingColumnJointProfile]

end Atlas.Fischer
