import Atlas.Rudvalis.LocalFusionObstruction
import Atlas.Rudvalis.GaussianPrimeOrder
import Atlas.Rudvalis.OrthogonalCrossCount

/-! The arithmetic conclusion is conditional on the explicit geometric orbit-size
alternatives and the coordinate-complement containment; those geometric inputs
are not asserted by this module. -/
namespace Atlas.Rudvalis

theorem localFusion_first_third_orthogonal :
    CrossOrthogonal (coordinateCross (localFusionSourceCoordinate 0))
      (coordinateCross (localFusionSourceCoordinate 2)) := by
  apply (coordinateFrame_orthogonal_iff _ _ (coordinateCross_mem _) (coordinateCross_mem _)).mpr
  intro h
  rcases (coordinateCross_eq_iff _ _).mp h with h|h
  · exact (by decide +kernel : localFusionSourceCoordinate 0≠localFusionSourceCoordinate 2) h
  · have hn : codeI.val.right (localFusionSourceCoordinate 0)≠localFusionSourceCoordinate 2 := by
      rw [codeI_coordinate]
      decide +kernel
    exact hn h

 theorem localFusion_coordinate_complement_card :
    (coordinateFrame\{coordinateCross (localFusionSourceCoordinate 0)}).ncard=27 := by
  rw [Set.ncard_sdiff_singleton_of_mem (coordinateCross_mem _)]
  change Nat.card coordinateFrame-1=27
  rw [coordinateFrame_card]

/-- Explicit arithmetic-fusion criterion. The two hypotheses about the orbit are
geometric obligations, rather than unproved claims about the actual stabilizer. -/
theorem localFusion_full_orthogonal_orbit (K : Subgroup gaussianLatticeGroup)
    (hfix : ∀g : K,g • coordinateCross (localFusionSourceCoordinate 0)=
      coordinateCross (localFusionSourceCoordinate 0))
    (ht : localFusionT∈K)
    (hcoordinate : coordinateFrame\{coordinateCross (localFusionSourceCoordinate 0)} ⊆
      MulAction.orbit K (coordinateCross (localFusionSourceCoordinate 2)))
    (hsizes : Nat.card (MulAction.orbit K (coordinateCross (localFusionSourceCoordinate 2)))=27 ∨
      Nat.card (MulAction.orbit K (coordinateCross (localFusionSourceCoordinate 2)))=219 ∨
      Nat.card (MulAction.orbit K (coordinateCross (localFusionSourceCoordinate 2)))=1563 ∨
      Nat.card (MulAction.orbit K (coordinateCross (localFusionSourceCoordinate 2)))=1755) :
    MulAction.orbit K (coordinateCross (localFusionSourceCoordinate 2))=
      {c : MinimalCross | CrossOrthogonal (coordinateCross (localFusionSourceCoordinate 0)) c} := by
  have hd : Nat.card (MulAction.orbit K (coordinateCross (localFusionSourceCoordinate 2)))∣Nat.card K := by
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K
      (coordinateCross (localFusionSourceCoordinate 2)))
    rw [Nat.card_prod] at h
    exact ⟨_,h.symm⟩
  have hsize := gaussian_fusion_size_alternatives K _ hsizes hd
  rcases hsize with h27|h1755
  · exfalso
    apply localFusion_no_coordinate_complement_orbit K hfix ht
    symm
    apply Set.eq_of_subset_of_ncard_le hcoordinate
    rw [←Nat.card_coe_set_eq,h27,localFusion_coordinate_complement_card]
  · apply Set.eq_of_subset_of_ncard_le
    · intro c hc
      obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hc
      have h := (crossOrthogonal_gaussian g.val _ _).mpr localFusion_first_third_orthogonal
      change CrossOrthogonal (g • coordinateCross (localFusionSourceCoordinate 0))
        (g • coordinateCross (localFusionSourceCoordinate 2)) at h
      rw [hfix g] at h
      exact h
    · change Nat.card (OrthogonalCrosses (coordinateCross (localFusionSourceCoordinate 0)))≤
        Nat.card (MulAction.orbit K (coordinateCross (localFusionSourceCoordinate 2)))
      rw [coordinate_orthogonal_crosses_card,h1755]
    · apply Set.finite_of_ncard_pos
      change 0<Nat.card (OrthogonalCrosses (coordinateCross (localFusionSourceCoordinate 0)))
      rw [coordinate_orthogonal_crosses_card]
      decide

end Atlas.Rudvalis
