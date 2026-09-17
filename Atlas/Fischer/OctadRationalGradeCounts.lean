import Atlas.Fischer.OctadRationalGrading

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private theorem restriction_indicator_sum (O S : Finset Omega) :
    (∑ D : Octad, if D.val ∩ O=S then 1 else 0 : ℕ) = octadRestrictionCount O S := by
  rw [←Finset.sum_subtype octads (fun _ => Iff.rfl)
    (fun D : Finset Omega => if D ∩ O=S then (1 : ℕ) else 0)]
  simp only [octadRestrictionCount, Finset.card_eq_sum_ones, Finset.sum_filter]

private theorem complement_label_eq (O D S : Finset Omega) (hSO : S ⊆ O) :
    O \ (D ∩ O)=S ↔ D ∩ O=O \ S := by
  constructor
  · intro h
    have hh := congrArg (fun T => O \ T) h
    simpa only [Finset.sdiff_sdiff_eq_self Finset.inter_subset_right] using hh
  · intro h
    rw [h,Finset.sdiff_sdiff_eq_self hSO]

set_option backward.isDefEq.respectTransparency false in
/-- Count rational directions from the actual marked octad intersections. -/
theorem octadRationalGradeIndex_card (O : Octad) (S : Finset Omega) (hSO : S ⊆ O.val) :
    Nat.card (OctadRationalGradeIndex O S) =
      24*(if ∅=S then 1 else 0) + 24*(if O.val=S then 1 else 0) +
        octadRestrictionCount O.val S + octadRestrictionCount O.val (O.val \ S) := by
  classical
  letI : Fintype (OctadRationalGradeIndex O S) := Fintype.ofFinite _
  have hc : Nat.card (OctadRationalGradeIndex O S) =
      ∑ p : RationalCoordinateIndex, if octadRationalLabel O p=S then 1 else 0 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [hc,Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_two]
  rw [Fintype.sum_sum_type]
  simp only [octadRationalLabel_axis_real,octadRationalLabel_axis_theta,
    octadRationalLabel_octad_real,octadRationalLabel_octad_theta]
  simp_rw [complement_label_eq O.val _ S hSO]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
    restriction_indicator_sum O.val S,restriction_indicator_sum O.val (O.val \ S)]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  have hO : Fintype.card Omega=24 := rfl
  rw [hO]
  by_cases hs : ∅ = S
  · simp only [hs, ↓reduceIte, Finset.sum_const, Finset.card_univ, smul_eq_mul, hO]
    omega
  · simp only [hs, ↓reduceIte, Finset.sum_const, Finset.card_univ, smul_eq_mul, hO]
    omega

private theorem octad_nonempty (O : Octad) : O.val ≠ ∅ := by
  intro h
  have hc := octad_size O.val O.prop
  rw [h,Finset.card_empty] at hc
  omega

theorem octadRationalGrade_empty_dimension (O : Octad) :
    Module.finrank ℚ (octadRationalGrade O ∅) = 55 := by
  rw [octadRationalGrade_finrank,octadRationalGradeIndex_card O ∅ (Finset.empty_subset _)]
  simp [octad_nonempty O,octadRestrictionCount_empty O.val O.prop,
    octadRestrictionCount_self O.val O.prop]

theorem octadRationalGrade_full_dimension (O : Octad) :
    Module.finrank ℚ (octadRationalGrade O O.val) = 55 := by
  rw [octadRationalGrade_finrank,octadRationalGradeIndex_card O O.val (Finset.Subset.refl _)]
  simp [Ne.symm (octad_nonempty O),octadRestrictionCount_empty O.val O.prop,
    octadRestrictionCount_self O.val O.prop]

theorem octadRationalGrade_duad_dimension (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card=2) :
    Module.finrank ℚ (octadRationalGrade O S) = 16 := by
  rw [octadRationalGrade_finrank,octadRationalGradeIndex_card O S hSO]
  have hn : ∅ ≠ S := by intro h; have := congrArg Finset.card h; simp only [Finset.card_empty,hS] at this; omega
  have ho : O.val ≠ S := by intro h; have := congrArg Finset.card h; rw [octad_size O.val O.prop,hS] at this; omega
  have hd : (O.val \ S).card=6 := by rw [Finset.card_sdiff_of_subset hSO,octad_size O.val O.prop,hS]
  simp [hn,ho,octadRestrictionCount_duad O.val S O.prop hSO hS,
    octadRestrictionCount_six O.val (O.val \ S) O.prop hd]

theorem octadRationalGrade_six_dimension (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card=6) :
    Module.finrank ℚ (octadRationalGrade O S) = 16 := by
  rw [octadRationalGrade_finrank,octadRationalGradeIndex_card O S hSO]
  have hn : ∅ ≠ S := by intro h; have := congrArg Finset.card h; simp only [Finset.card_empty,hS] at this; omega
  have ho : O.val ≠ S := by intro h; have := congrArg Finset.card h; rw [octad_size O.val O.prop,hS] at this; omega
  have hd : (O.val \ S).card=2 := by rw [Finset.card_sdiff_of_subset hSO,octad_size O.val O.prop,hS]
  simp [hn,ho,octadRestrictionCount_six O.val S O.prop hS,
    octadRestrictionCount_duad O.val (O.val \ S) O.prop Finset.sdiff_subset hd]

theorem octadRationalGrade_tetrad_dimension (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card=4) :
    Module.finrank ℚ (octadRationalGrade O S) = 8 := by
  rw [octadRationalGrade_finrank,octadRationalGradeIndex_card O S hSO]
  have hn : ∅ ≠ S := by intro h; have := congrArg Finset.card h; simp only [Finset.card_empty,hS] at this; omega
  have ho : O.val ≠ S := by intro h; have := congrArg Finset.card h; rw [octad_size O.val O.prop,hS] at this; omega
  have hd : (O.val \ S).card=4 := by rw [Finset.card_sdiff_of_subset hSO,octad_size O.val O.prop,hS]
  simp [hn,ho,octadRestrictionCount_tetrad O.val S O.prop hSO hS,
    octadRestrictionCount_tetrad O.val (O.val \ S) O.prop Finset.sdiff_subset hd]

end Atlas.Fischer
