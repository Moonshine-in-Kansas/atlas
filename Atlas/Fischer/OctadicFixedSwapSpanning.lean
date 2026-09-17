import Atlas.Fischer.OctadicFixedSwapVectors

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octadExteriorAxisSum_mem_fortySix {O : Octad} (Q : OctadCalibration O) :
    octadExteriorAxisSum O ∈ octadicFortySixSpace Q := by
  unfold octadExteriorAxisSum
  apply (octadicFortySixSpace Q).sum_mem
  intro i hi
  exact Submodule.subset_span (Or.inl ⟨⟨i, Finset.mem_compl.mp hi⟩, rfl⟩)

theorem rootMap_octadic_exteriorAxisSum_fixed {O : Octad} (Q : OctadCalibration O) :
    rootMap (octadicRoot Q 0) (octadExteriorAxisSum O) = octadExteriorAxisSum O := by
  have hp : hermitian (rootMap (octadicRoot Q 0) (octadExteriorAxisSum O))
      (octadExteriorAxisSum O) = 2 := by
    conv_lhs => lhs; rhs; rw [octadExteriorAxisSum]
    rw [rootMap_sum, hermitian_sum_left]
    have hh (i : Omega) (hi : i ∈ O.valᶜ) :
        hermitian (rootMap (octadicRoot Q 0) (u i)) (octadExteriorAxisSum O) = 1 / 8 := by
      rw [rootMap_octadic_outside_axis Q ⟨i, Finset.mem_compl.mp hi⟩,
        hermitian_smul_left, hermitian_sub_left, octadExteriorAxisSum_norm]
      change (1 / 16 : Scalar) * (2 - hermitian
        (octadicHyperplanePart Q (octadEvaluation O ⟨i, Finset.mem_compl.mp hi⟩))
        (∑ j ∈ O.valᶜ, u j)) = 1 / 8
      rw [hermitian_hyperplanePart_axisSum]
      norm_num
    rw [Finset.sum_congr rfl hh, Finset.sum_const, Finset.card_compl,
      octad_size O.val O.property]
    have hc : Fintype.card Omega = 24 := by decide
    rw [hc]
    norm_num
  have hnorm := rootMap_octadic_fortySix_antiunitary Q _ (octadExteriorAxisSum_mem_fortySix Q)
    _ (octadExteriorAxisSum_mem_fortySix Q)
  rw [octadExteriorAxisSum_norm] at hnorm
  have hp' : hermitian (octadExteriorAxisSum O)
      (rootMap (octadicRoot Q 0) (octadExteriorAxisSum O)) = 2 := by
    rw [← hermitian_star, hp]
    norm_num
  apply sub_eq_zero.mp
  apply (hermitian_self_eq_zero _).mp
  rw [hermitian_sub_left, hermitian_sub_right, hermitian_sub_right,
    hnorm, hp, hp', octadExteriorAxisSum_norm]
  norm_num

/-- The fixed vector, complementary-pair sums, and the actual swapped pairs. -/
def octadicFixedSwapGenerators {O : Octad} (Q : OctadCalibration O) : Set Coordinates :=
  {octadExteriorAxisSum O} ∪ Set.range (octadicComplementPairVector Q) ∪
    Set.range (octadicHyperplaneAxisVector Q) ∪ Set.range (octadicDifferencePairVector Q)

theorem octadicFixedSwap_span {O : Octad} (Q : OctadCalibration O) :
    Submodule.span Scalar (octadicFixedSwapGenerators Q) = octadicFortySixSpace Q := by
  let T := Submodule.span Scalar (octadicFixedSwapGenerators Q)
  have hs : octadExteriorAxisSum O ∈ T := Submodule.subset_span (Or.inl (Or.inl (Or.inl rfl)))
  have hc (b : OctadShortenedHyperplane O) : octadicComplementPairVector Q b ∈ T :=
    Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨b, rfl⟩)))
  have hw (b : OctadShortenedHyperplane O) : octadicHyperplaneAxisVector Q b ∈ T :=
    Submodule.subset_span (Or.inl (Or.inr ⟨b, rfl⟩))
  have hd (b : OctadShortenedHyperplane O) : octadicDifferencePairVector Q b ∈ T :=
    Submodule.subset_span (Or.inr ⟨b, rfl⟩)
  have hyS (b : OctadShortenedHyperplane O) :
      calibratedHyperplaneVector Q b ∈ octadicFortySixSpace Q :=
    Submodule.subset_span (Or.inr ⟨b, rfl⟩)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ((rfl | ⟨b, rfl⟩) | ⟨b, rfl⟩) | ⟨b, rfl⟩
    · exact octadExteriorAxisSum_mem_fortySix Q
    · exact (octadicFortySixSpace Q).add_mem (hyS b) (hyS _)
    · rw [← rootMap_octadic_differencePair]
      exact rootMap_octadic_fortySix_invariant Q ((octadicFortySixSpace Q).sub_mem (hyS b) (hyS _))
    · exact (octadicFortySixSpace Q).sub_mem (hyS b) (hyS _)
  · apply Submodule.span_le.mpr
    have hty (b : OctadShortenedHyperplane O) :
        rootMap (octadicRoot Q 0) (calibratedHyperplaneVector Q b) ∈ T := by
      rw [rootMap_octadic_hyperplane_split]
      exact T.smul_mem _ (T.add_mem (hw b) (hc b))
    have htY (χ : OctadicCharacter O) : rootMap (octadicRoot Q 0) (octadicHyperplanePart Q χ) ∈ T := by
      rw [octadicHyperplanePart, rootMap_sum]
      apply T.sum_mem
      intro b hb
      rw [rootMap_smul]
      exact T.smul_mem _ (hty b)
    intro x hx
    rcases hx with ⟨i, rfl⟩ | ⟨b, rfl⟩
    · have hi : u i.val ∈ octadicFortySixSpace Q := Submodule.subset_span (Or.inl ⟨i, rfl⟩)
      change u i.val ∈ T
      rw [← rootMap_octadic_fortySix_involutive Q _ hi, rootMap_octadic_outside_axis,
        rootMap_smul, rootMap_sub, rootMap_octadic_exteriorAxisSum_fixed]
      exact T.smul_mem _ (T.sub_mem hs (htY _))
    · have he : calibratedHyperplaneVector Q b = (1 / 2 : Scalar) •
          (octadicComplementPairVector Q b + octadicDifferencePairVector Q b) := by
        unfold octadicComplementPairVector octadicDifferencePairVector
        module
      rw [he]
      exact T.smul_mem _ (T.add_mem (hc b) (hd b))

end Atlas.Fischer
