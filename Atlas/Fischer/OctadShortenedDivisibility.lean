import Atlas.Fischer.OctadShortenedCode
import Atlas.Fischer.ParkerTriplyEvenSubcodes

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem octadComplementWord_weight (O : Octad) :
    hammingNorm (octadComplementWord O).val = 16 := by
  have h := complement_weight (octadWord O).val
  have he : (octadComplementWord O).val = (octadWord O).val + allOnes := by
    change allOnes + (octadWord O).val = _
    exact add_comm _ _
  rw [← he, octadWord_weight] at h
  omega

theorem octadShortened_overlap_complement (O : Octad) (c : octadShortenedCode O) :
    overlap c.val.val (octadComplementWord O).val = hammingNorm c.val.val := by
  classical
  rw [overlap_eq_sum, hammingNorm_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ O.val
  · have hz := (mem_octadShortenedCode O c.val).mp c.prop i hi
    simp [octadComplementWord_apply, hi, hz]
  · simp [octadComplementWord_apply, hi]

theorem octadShortened_complement_weights (O : Octad) (c : octadShortenedCode O) :
    hammingNorm (c + octadShortenedOne O).val.val + hammingNorm c.val.val = 16 := by
  have h := binary_weight_add c.val.val (octadComplementWord O).val
  rw [octadShortened_overlap_complement, octadComplementWord_weight] at h
  change hammingNorm (c.val.val + (octadComplementWord O).val) + hammingNorm c.val.val = 16
  omega

theorem octadShortened_weights (O : Octad) (c : octadShortenedCode O) :
    hammingNorm c.val.val = 0 ∨ hammingNorm c.val.val = 8 ∨ hammingNorm c.val.val = 16 := by
  have h := octadShortened_complement_weights O c
  have hc := golay_weights c.val
  have hd := golay_weights (c + octadShortenedOne O).val
  omega

theorem octadShortened_weight_dvd (O : Octad) (c : octadShortenedCode O) :
    8 ∣ hammingNorm c.val.val := by
  rcases octadShortened_weights O c with h | h | h <;> rw [h] <;> decide

theorem octadShortened_overlap_dvd (O : Octad) (a b : octadShortenedCode O) :
    4 ∣ overlap a.val.val b.val.val := by
  let K := ParkerElementarySubcode.ofWeightDivisibility (octadShortenedCode O)
    (octadShortened_weight_dvd O)
  have hz := K.commutator_zero a b
  change ((overlap a.val.val b.val.val / 2 : ℕ) : Bit) = 0 at hz
  rw [ZMod.natCast_eq_zero_iff_even] at hz
  obtain ⟨k,hk⟩ := even_iff_two_dvd.mp hz
  obtain ⟨j,hj⟩ := golay_overlap_two_dvd a.val b.val
  exact ⟨k, by omega⟩

theorem octadShortened_triple_dvd (O : Octad) (a b c : octadShortenedCode O) :
    2 ∣ parkerTripleCount a.val.val b.val.val c.val.val := by
  let K := ParkerElementarySubcode.ofWeightDivisibility (octadShortenedCode O)
    (octadShortened_weight_dvd O)
  have hz := K.associator_zero a b c
  rw [← parkerTripleCount_cast, ZMod.natCast_eq_zero_iff_even] at hz
  exact even_iff_two_dvd.mp hz

end Atlas.Fischer
