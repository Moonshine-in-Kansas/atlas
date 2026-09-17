import Atlas.Fischer.BasicSupportSeparation

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- A displayed root commuting with twenty-three marked basic axes must itself
be basic; actual octadic and duadic supports have only eight and two points. -/
theorem displayedRoot_basic_support_except_one (t : ReflectingRootParameter) (a : Omega)
    (h : ∀ i : Omega, i ≠ a → hermitian (basicAxis i) (reflectingRootParameterVector t) ≠ 0) :
    ∃ j : Omega, t=.inl j := by
  classical
  rcases t with j | (t | t)
  · exact ⟨j,rfl⟩
  · have hu : Finset.univ.erase a ⊆ t.1.val := by
      intro i hi
      have hh := h i (Finset.mem_erase.mp hi).1
      by_contra hn
      change hermitian (basicAxis i) (octadicRoot (chosenOctadCalibration t.1) t.2) ≠ 0 at hh
      rw [hermitian_basicAxis_octadic,if_neg hn] at hh
      exact hh rfl
    have hc := Finset.card_le_card hu
    rw [Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,
      show Fintype.card Omega=24 from rfl,octad_size t.1.val t.1.property] at hc
    omega
  · have hu : Finset.univ.erase a ⊆ t.1.val := by
      intro i hi
      have hh := h i (Finset.mem_erase.mp hi).1
      by_contra hn
      change hermitian (basicAxis i) (chosenDuadicRoot t.1 t.2) ≠ 0 at hh
      rw [hermitian_basicAxis_duadic,if_neg hn] at hh
      exact hh rfl
    have hc := Finset.card_le_card hu
    rw [Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,
      show Fintype.card Omega=24 from rfl,t.1.property] at hc
    omega

end Atlas.Fischer
