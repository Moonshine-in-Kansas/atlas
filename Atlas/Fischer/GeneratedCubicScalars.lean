import Atlas.Fischer.RootRayProductOrders
import Atlas.Fischer.ReflectingNonrealExistence
import Atlas.Fischer.ParkerAlgebraRepresentation
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual displayed octadic character family realizes a nonreal pairing. -/
theorem displayedRoots_exist_nonreal : ∃ i j : ReflectingRootParameter,
    star (hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)) ≠
      hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j) := by
  classical
  obtain ⟨Ov,hOv⟩ := Finset.card_pos.mp (show 0 < octads.card by rw [octads_card]; decide)
  let O : Octad := ⟨Ov,hOv⟩
  obtain ⟨F,hF⟩ := octad_exists_disjoint O
  obtain ⟨χ,ψ,h⟩ := octadicRoot_disjoint_exists_nonreal O F hF
    (chosenOctadCalibration O) (chosenOctadCalibration F)
  exact ⟨.inr (.inl ⟨O,χ⟩),.inr (.inl ⟨F,ψ⟩),h⟩

/-- A nonidentity cubic scalar is a literal square of two displayed algebra
reflections. No scalar-kernel or full-automorphism identification is used. -/
theorem generated_nontrivial_cubic_scalar : ∃ a : Mu3, a ≠ 1 ∧
    scalarAlgebraRepresentation a ∈ rootGeneratedAlgebraGroup := by
  obtain ⟨i,j,hn⟩ := displayedRoots_exist_nonreal
  have hij : i ≠ j := by
    intro h
    subst j
    rw [(reflectingRootParameter_isReflectingRoot i).1.1] at hn
    norm_num at hn
  have hzero : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j) ≠ 0 := by
    intro h
    rw [h,star_zero] at hn
    exact hn rfl
  obtain hz | ⟨a,ha⟩ := reflectingRoot_pairing_zero_or_mu3 _ _
    (reflectingRootParameter_isReflectingRoot i) (reflectingRootParameter_isReflectingRoot j)
    (reflectingRootParameter_distinct_phases i j hij)
  · exact (hzero hz).elim
  have ha3 : (a.val.val : Scalar)^3=1 := (mem_rootsOfUnity' _ _).mp a.property
  refine ⟨a,?_,?_⟩
  · intro h
    rw [ha,h] at hn
    simpa using hn
  · have he : (displayedRootAutomorphism i * displayedRootAutomorphism j)^2 =
        scalarAlgebraRepresentation a := by
      apply Subtype.ext
      apply Equiv.ext
      intro x
      change rootMap (reflectingRootParameterVector i) (rootMap (reflectingRootParameterVector j)
        (rootMap (reflectingRootParameterVector i) (rootMap (reflectingRootParameterVector j) x))) =
          (a.val.val : Scalar) • x
      rw [reflectingRoot_unit_product_square _ _ (reflectingRootParameter_isReflectingRoot i)
        (reflectingRootParameter_isReflectingRoot j) (by rw [ha]; exact ha3),ha]
    rw [← he]
    exact rootGeneratedAlgebraGroup.pow_mem
      (rootGeneratedAlgebraGroup.mul_mem (displayedRootAutomorphism_mem i) (displayedRootAutomorphism_mem j)) 2

/-- Prime order three upgrades the actual nontrivial generated scalar to all
cubic scalar maps. This containment is independent of the full ray kernel. -/
theorem scalarAlgebraRepresentation_mem_generated (a : Mu3) :
    scalarAlgebraRepresentation a ∈ rootGeneratedAlgebraGroup := by
  haveI : Fact (Nat.card Mu3).Prime := ⟨by rw [mu3_card]; decide⟩
  let K : Subgroup Mu3 := rootGeneratedAlgebraGroup.comap scalarAlgebraRepresentation
  obtain ⟨b,hb,hbg⟩ := generated_nontrivial_cubic_scalar
  rcases K.eq_bot_or_eq_top_of_prime_card with hK | hK
  · have hmem : b ∈ K := hbg
    rw [hK] at hmem
    exact (hb hmem).elim
  · have hmem : a ∈ K := by rw [hK]; trivial
    exact hmem

theorem scalarAlgebraRepresentation_range_le_generated :
    scalarAlgebraRepresentation.range ≤ rootGeneratedAlgebraGroup := by
  rintro x ⟨a,rfl⟩
  exact scalarAlgebraRepresentation_mem_generated a

end Atlas.Fischer
