import Atlas.Fischer.OctadDiamondClosure
import Atlas.Fischer.ParkerCenter
import Atlas.Algebra.BinaryContractionExponent

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

private theorem cancelPair (x y z : golay) : x + y + (x + y + z) = z := by
  calc
    _ = (x + x) + (y + y) + z := by abel
    _ = z := by simp only [parkerGolay_add_self, zero_add]

theorem octadTriangle_delta (D E F : Octad)
    (h : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine) :
    octadWord D + octadWord E + octadWord F = (octadDelta D E : Bit) • golayOne := by
  classical
  rcases (mem_allOneCodeLine _).mp h with h | h
  · have hc := congrArg (fun z => octadWord D + octadWord E + z) h
    have hf : octadWord F = octadWord D + octadWord E := by
      simpa only [cancelPair, add_zero] using hc
    have h4 : (D.val ∩ E.val).card = 4 := by
      simpa only [signedOctadIntersection, signedOctadSupport_canonical] using
        octadWord_sum_weight F D E hf
    have h0 : (D.val ∩ E.val).card ≠ 0 := by omega
    rw [h]
    simp [octadDelta, h0]
  · have hc := congrArg (fun z => octadWord D + octadWord E + z) h
    have hf : octadWord F = octadWord D + octadWord E + golayOne := by
      simpa only [cancelPair] using hc
    have h0 : (D.val ∩ E.val).card = 0 := by
      simpa only [signedOctadIntersection, signedOctadSupport_canonical] using
        octadWord_complementary_sum_weight F D E hf
    rw [h]
    simp [octadDelta, h0]

theorem octad_contraction_delta_parity (D E F G H J G' H' J' : Octad)
    (hDE : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine)
    (hGH : octadWord G + octadWord H + octadWord J ∈ allOneCodeLine)
    (hDG : octadWord D + octadWord G + octadWord G' ∈ allOneCodeLine)
    (hEH : octadWord E + octadWord H + octadWord H' ∈ allOneCodeLine)
    (hFJ : octadWord F + octadWord J + octadWord J' ∈ allOneCodeLine) :
    ((octadDelta G H + octadDelta D G + octadDelta E H +
      octadDelta F J + octadDelta G' H' : ℕ) : Bit) = (octadDelta D E : Bit) := by
  have hlast := octad_contraction_triangle_closure D E F G H J G' H' J' hDE hGH hDG hEH hFJ
  have hs : (octadDelta D E : Bit) + (octadDelta G H : Bit) +
      (octadDelta D G : Bit) + (octadDelta E H : Bit) + (octadDelta F J : Bit) =
        (octadDelta G' H' : Bit) := by
    apply (smul_left_injective Bit parkerGolayOne_ne_zero)
    simp only [add_smul]
    rw [← octadTriangle_delta D E F hDE, ← octadTriangle_delta G H J hGH,
      ← octadTriangle_delta D G G' hDG, ← octadTriangle_delta E H H' hEH,
      ← octadTriangle_delta F J J' hFJ, ← octadTriangle_delta G' H' J' hlast]
    calc
      _ = (octadWord D + octadWord D) + (octadWord E + octadWord E) +
          (octadWord F + octadWord F) + (octadWord G + octadWord G) +
          (octadWord H + octadWord H) + (octadWord J + octadWord J) +
          (octadWord G' + octadWord H' + octadWord J') := by abel
      _ = _ := by simp only [parkerGolay_add_self, zero_add]
  simp only [Nat.cast_add]
  have hz : (2 : Bit) = 0 := by decide
  linear_combination (norm := ring_nf) hs
  all_goals simp only [hz, mul_zero, add_zero, zero_add, sub_zero]

/-- The manuscript exponent is an actual integer in {0,1,2}, derived from
the retained Golay triangle relations and the binary type bounds. -/
theorem octad_contraction_exponent (D E F G H J G' H' J' : Octad)
    (hDE : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine)
    (hGH : octadWord G + octadWord H + octadWord J ∈ allOneCodeLine)
    (hDG : octadWord D + octadWord G + octadWord G' ∈ allOneCodeLine)
    (hEH : octadWord E + octadWord H + octadWord H' ∈ allOneCodeLine)
    (hFJ : octadWord F + octadWord J + octadWord J' ∈ allOneCodeLine) :
    let s := octadDelta G H + octadDelta D G + octadDelta E H +
      octadDelta F J + octadDelta G' H'
    octadDelta D E ≤ s ∧ s - octadDelta D E = 2 * ((s - octadDelta D E) / 2) ∧
      (s - octadDelta D E) / 2 ≤ 2 := by
  have hb := octad_contraction_delta_parity D E F G H J G' H' J' hDE hGH hDG hEH hFJ
  have hv := congrArg (fun z : Bit => z.val) hb
  simp only [ZMod.val_natCast] at hv
  have he : octadDelta D E % 2 = octadDelta D E :=
    Nat.mod_eq_of_lt (by have h := octadDelta_le_one D E; omega)
  rw [he] at hv
  exact Atlas.Algebra.binary_contraction_exponent _ _ _ _ _ _
    (octadDelta_le_one D E) (octadDelta_le_one G H) (octadDelta_le_one D G)
    (octadDelta_le_one E H) (octadDelta_le_one F J) (octadDelta_le_one G' H') hv

end Atlas.Fischer
