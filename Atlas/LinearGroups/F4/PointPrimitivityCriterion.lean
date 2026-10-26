import Atlas.LinearGroups.F4.PointOpposition
import Atlas.GroupTheory.PrimitivePointChainTransport

/-! Conditional wiring of the geometric primitivity argument. The remaining
escape obligation is explicit, and no primitivity or simplicity is asserted
without it. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

/-- It suffices to produce finite stabilizer-move escapes for nonopposite
points at C₀. Actual transitivity transports them to every pair. -/
theorem whiteZeroPoints_primitive_of_base_escape
    (escape : ∀ x : WhiteZeroPoints F, x≠parabolicPoint →
      ¬PointsOpposite parabolicPoint x →
      ∃ z : WhiteZeroPoints F,
        Atlas.GroupTheory.StabilizerMoveChain (Model F) parabolicPoint x z ∧
          PointsOpposite parabolicPoint z) :
    MulAction.IsPreprimitive (Model F) (WhiteZeroPoints F) := by
  classical
  apply Atlas.GroupTheory.primitive_of_nonrelated_orbit_and_chains
    (parabolicPoint (F:=F)) (fun x y => ¬PointsOpposite x y)
  · intro x y hxy hyx
    exact hxy (pointsOpposite_symm.mpr hyx)
  · intro x y z hy hz
    exact opposite_points_stabilizer_transitive x y z (not_not.mp hy) (not_not.mp hz)
  · intro x y _ _
    obtain ⟨z,hxz,hyz⟩ := pointsOpposite_common x y
    exact ⟨z,not_not.mpr hxz,not_not.mpr hyz⟩
  · intro x y hne hnon
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) x parabolicPoint
    have hne' : g • y≠parabolicPoint := by
      intro h
      apply hne
      have he := congrArg (fun p : WhiteZeroPoints F => g⁻¹ • p) (hg.trans h.symm)
      simpa only [inv_smul_smul] using he
    have hnon' : ¬PointsOpposite parabolicPoint (g • y) := by
      rw [←hg,pointsOpposite_smul_iff]
      exact hnon
    obtain ⟨z,hchain,hop⟩ := escape (g • y) hne' hnon'
    have hp : g⁻¹ • (parabolicPoint (F:=F))=x := by
      rw [←hg,inv_smul_smul]
    refine ⟨g⁻¹ • z,?_,?_⟩
    · have hc := Atlas.GroupTheory.stabilizerMoveChain_smul g⁻¹ hchain
      simpa only [hp,inv_smul_smul] using hc
    · apply not_not.mpr
      have ho := (pointsOpposite_smul_iff g⁻¹ parabolicPoint z).mpr hop
      simpa only [hp] using ho

end Atlas.F4
