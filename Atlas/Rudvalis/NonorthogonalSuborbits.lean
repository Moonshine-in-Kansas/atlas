import Atlas.Rudvalis.FourSuborbitDivisibility
import Atlas.Rudvalis.HeavyRowKernelOrbit

namespace Atlas.Rudvalis

 theorem heavyCross_rowReference_orbit_divisible (v : HeavyCrosses) :
    128∣Nat.card (MulAction.orbit codeRowReferenceStabilizer (shellPieceCrossMap heavyShellPiece v)) := by
  apply Atlas.suborbit_card_divisible codeRowReferenceStabilizer _ 128
  rw [codeRowReferenceStabilizer_order,heavyCross_rowKernel_stabilizer_order]

 theorem heavy_reference_orbit_divisible (v : HeavyCrosses) :
    128∣Nat.card (MulAction.orbit codeReferenceStabilizer (shellPieceCrossMap heavyShellPiece v)) := by
  refine Atlas.GroupTheory.invariant_card_dvd_of_orbits
    (G:=codeRowReferenceStabilizer) _ (Set.toFinite _) ?_ 128 ?_
  · intro g d hd
    exact MulAction.mapsTo_smul_orbit (rowReferenceToCodeReference g) _ hd
  · intro d hd
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hd
    obtain ⟨w,hw⟩ := shellPieceCross_range_stable heavyShellPiece g.val _ ⟨v,rfl⟩
    change 128∣Nat.card (MulAction.orbit codeRowReferenceStabilizer (g.val • shellPieceCrossMap heavyShellPiece v))
    rw [←hw]
    exact heavyCross_rowReference_orbit_divisible w

/-- Every actual nonorthogonal suborbit, other than the base cross, has size divisible by 64. -/
 theorem codeReference_nonorthogonal_orbit_divisible (c : MinimalCross)
    (hne : c≠localReferenceCross) (hn : ¬CrossOrthogonal localReferenceCross c) :
    64∣Nat.card (MulAction.orbit codeReferenceStabilizer c) := by
  rcases minimalCross_piece_cases c with ⟨v,rfl⟩|⟨v,rfl⟩|⟨v,rfl⟩
  · exact (hn ((coordinateFrame_orthogonal_iff _ _
      (localReferenceCross_eq ▸ coordinateCross_mem _) ⟨v,rfl⟩).mpr hne.symm)).elim
  · exact four_reference_orbit_divisible v hn
  · exact dvd_trans (by decide :64∣128) (heavy_reference_orbit_divisible v)

end Atlas.Rudvalis
