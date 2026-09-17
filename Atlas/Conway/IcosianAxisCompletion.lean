import Atlas.Conway.IcosianAxisPairCompletion
import Atlas.Conway.IcosianAxisNeighborCount

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- Every root line perpendicular to the first coordinate axis has exactly one
third root line perpendicular to both. The completion is constructed inside the actual lattice. -/
theorem icosianRootAxis_completion (p : IcosianAxisNeighbor) :
    ∃! q : IcosianRootPoint,
      IcosianRootPointOrthogonal (icosianRootAxisPoint 0) q ∧
      IcosianRootPointOrthogonal p.val q := by
  obtain ⟨r,hr⟩ := icosianRootToPoint_surjective p.val
  have hz := (icosianRootAxisPoint_orthogonal_iff 0 r).mp (hr.symm ▸ p.property)
  rcases icosianRoot_zero_structure r hz with h1 | h2 | hn
  · have hp : p.val=icosianRootAxisPoint 2 := by
      rw [← hr]
      apply icosianRootPoint_of_single_support r 2
      intro i hi
      fin_cases i
      · exact hz
      · exact h1
      · exact (hi rfl).elim
    refine ⟨icosianRootAxisPoint 1,⟨icosianRootAxisPoints_orthogonal 0 1 (by decide),?_⟩,?_⟩
    · rw [hp]
      exact icosianRootAxisPoints_orthogonal 2 1 (by decide)
    · intro q hq
      rw [hp] at hq
      exact icosianRootAxisPair_complement_unique 0 2 1 (by decide) (by decide) (by decide) q hq.1 hq.2
  · have hp : p.val=icosianRootAxisPoint 1 := by
      rw [← hr]
      apply icosianRootPoint_of_single_support r 1
      intro i hi
      fin_cases i
      · exact hz
      · exact (hi rfl).elim
      · exact h2
    refine ⟨icosianRootAxisPoint 2,⟨icosianRootAxisPoints_orthogonal 0 2 (by decide),?_⟩,?_⟩
    · rw [hp]
      exact icosianRootAxisPoints_orthogonal 1 2 (by decide)
    · intro q hq
      rw [hp] at hq
      exact icosianRootAxisPair_complement_unique 0 1 2 (by decide) (by decide) (by decide) q hq.1 hq.2
  · obtain ⟨b,hb⟩ := icosianEdgeRootBase_reconstruct r hz hn.1 hn.2
    have hp : p.val=icosianRootToPoint (icosianEdgeRootBase b) := by rw [hb,hr]
    let s := icosianEdgeRootBase (icosianEdgePartner b)
    refine ⟨icosianRootToPoint s,⟨?_,?_⟩,?_⟩
    · apply (icosianRootAxisPoint_orthogonal_iff 0 s).mpr
      exact icosianEdgeRootBase_zero _
    · rw [hp,icosianRootPointOrthogonal_iff]
      exact icosianEdgeRootBase_orthogonal_partner b
    · intro q hq
      obtain ⟨t,ht⟩ := icosianRootToPoint_surjective q
      have ht0 := (icosianRootAxisPoint_orthogonal_iff 0 t).mp (ht.symm ▸ hq.1)
      have hh := hq.2
      rw [hp,← ht,icosianRootPointOrthogonal_iff] at hh
      rw [← ht]
      apply Subtype.ext
      exact icosianEdgeRootBase_complement_unique b t ht0 hh

end Atlas.Conway
