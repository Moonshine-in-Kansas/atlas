import Atlas.Conway.IcosianAxisOrbitLinks
import Atlas.Conway.IcosianRootPointShapeNormCounts

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- A calculation on the nine labelled local pieces, not on root points. -/
theorem icosianNineNormFusion_cases : ∀ i j : Fin 9,
    icosianNineLocalNormValues i=icosianNineLocalNormValues j →
    icosianNineLocalShapeIndices i=icosianNineLocalShapeIndices j ∨
    (icosianNineLocalShapeIndices i=0 ∧ icosianNineLocalShapeIndices j=1 ∧ icosianNineLocalNormValues i=0) ∨
    (icosianNineLocalShapeIndices i=1 ∧ icosianNineLocalShapeIndices j=0 ∧ icosianNineLocalNormValues i=0) ∨
    (icosianNineLocalShapeIndices i=1 ∧ icosianNineLocalShapeIndices j=2 ∧ icosianNineLocalNormValues i=2) ∨
    (icosianNineLocalShapeIndices i=2 ∧ icosianNineLocalShapeIndices j=1 ∧ icosianNineLocalNormValues i=2) ∨
    (icosianNineLocalShapeIndices i=2 ∧ icosianNineLocalShapeIndices j=3 ∧ icosianNineLocalNormValues i=1) ∨
    (icosianNineLocalShapeIndices i=3 ∧ icosianNineLocalShapeIndices j=2 ∧ icosianNineLocalNormValues i=1) := by
  decide +kernel

theorem icosianSameAxisOrbit_of_norm (p q : IcosianRootPoint)
    (hn : icosianRootPointNormWord p 0=icosianRootPointNormWord q 0) :
    IcosianSameAxisOrbit p q := by
  obtain ⟨i,hpi,hni⟩ := icosianRootPointShapeNormLevel_nine_exhaustive p
  obtain ⟨j,hqj,hnj⟩ := icosianRootPointShapeNormLevel_nine_exhaustive q
  have hv := hni.symm.trans (hn.trans hnj)
  rcases icosianNineNormFusion_cases i j hv with hs | ⟨hi,hj,hv⟩ | ⟨hi,hj,hv⟩ |
    ⟨hi,hj,hv⟩ | ⟨hi,hj,hv⟩ | ⟨hi,hj,hv⟩ | ⟨hi,hj,hv⟩
  · exact icosianSameAxisOrbit_of_shape_norm _ p q hpi (hs.symm ▸ hqj) hn
  all_goals
    rw [hi] at hpi
    rw [hj] at hqj
  · exact icosianAxisOrbit_A_B p q hpi hqj (hni.trans hv) (hn.symm.trans (hni.trans hv))
  · exact (icosianAxisOrbit_A_B q p hqj hpi (hn.symm.trans (hni.trans hv)) (hni.trans hv)).symm
  · exact icosianAxisOrbit_B_C p q hpi hqj (hni.trans hv) (hn.symm.trans (hni.trans hv))
  · exact (icosianAxisOrbit_B_C q p hqj hpi (hn.symm.trans (hni.trans hv)) (hni.trans hv)).symm
  · exact icosianAxisOrbit_C_D p q hpi hqj (hni.trans hv) (hn.symm.trans (hni.trans hv))
  · exact (icosianAxisOrbit_C_D q p hqj hpi (hn.symm.trans (hni.trans hv)) (hni.trans hv)).symm

/-- The six intrinsic coordinate norm levels are exactly the orbits of the
full stabilizer of the first quaternionic root line. -/
theorem icosianFullAxisStabilizer_orbit (p : IcosianRootPoint) :
    MulAction.orbit icosianFullAxisStabilizer p=
      {q : IcosianRootPoint | icosianRootPointNormWord q 0=icosianRootPointNormWord p 0} := by
  ext q
  constructor
  · rintro ⟨g,rfl⟩
    exact icosianAxisStabilizer_point_norm g.val g.property p
  · intro hn
    exact MulAction.orbit_eq_iff.mp (icosianSameAxisOrbit_of_norm p q hn.symm).symm

theorem icosianFullAxisStabilizer_orbit_card (i : Fin 6) (p : IcosianRootPoint)
    (hp : icosianRootPointNormWord p 0=icosianRootCoordinateLevels i) :
    Nat.card (MulAction.orbit icosianFullAxisStabilizer p)=![1,10,160,80,32,32] i := by
  rw [Nat.card_congr (Equiv.setCongr (icosianFullAxisStabilizer_orbit p)),hp]
  exact icosianRootPointNormLevel_six_card i

end Atlas.Conway
