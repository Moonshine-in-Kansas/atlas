import Atlas.Fischer.MarkedBasicExtensions
import Atlas.Fischer.OctadAvoidance

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem displayedRoot_full_basic_support (t : ReflectingRootParameter)
    (h : ∀ i : Omega, hermitian (basicAxis i) (reflectingRootParameterVector t) ≠ 0) :
    ∃ j : Omega, t = .inl j := by
  classical
  rcases t with j | (t | t)
  · exact ⟨j, rfl⟩
  · have hu : Finset.univ ⊆ t.1.val := by
      intro i _
      by_contra hn
      have hh := h i
      change hermitian (basicAxis i) (octadicRoot (chosenOctadCalibration t.1) t.2) ≠ 0 at hh
      rw [hermitian_basicAxis_octadic, if_neg hn] at hh
      exact hh rfl
    have hc := Finset.card_le_card hu
    rw [Finset.card_univ, show Fintype.card Omega = 24 from rfl,
      octad_size t.1.val t.1.property] at hc
    omega
  · have hu : Finset.univ ⊆ t.1.val := by
      intro i _
      by_contra hn
      have hh := h i
      change hermitian (basicAxis i) (chosenDuadicRoot t.1 t.2) ≠ 0 at hh
      rw [hermitian_basicAxis_duadic, if_neg hn] at hh
      exact hh rfl
    have hc := Finset.card_le_card hu
    rw [Finset.card_univ, show Fintype.card Omega = 24 from rfl, t.1.property] at hc
    omega

/-- Actual octadic rays separate any two distinct marked basic axes. -/
theorem basic_axes_separated_by_octadic (i j : Omega) (hij : i ≠ j) :
    ∃ t : OctadicRootParameter,
      hermitian (basicAxis i) (octadicRoot (chosenOctadCalibration t.1) t.2) = 1 ∧
      hermitian (basicAxis j) (octadicRoot (chosenOctadCalibration t.1) t.2) = 0 := by
  classical
  obtain ⟨O, hi, hj, _⟩ := octad_contains_avoids_two {i} (by simp) j j
    (by simpa using hij.symm) (by simpa using hij.symm)
  refine ⟨⟨O, 0⟩, ?_, ?_⟩
  · rw [hermitian_basicAxis_octadic, if_pos (hi (by simp))]
  · rw [hermitian_basicAxis_octadic, if_neg hj]

end Atlas.Fischer
