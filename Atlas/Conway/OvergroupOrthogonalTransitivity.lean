import Atlas.Conway.OrthogonalOrbitFusion

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem strict_overgroup_orthogonal_orbit_full (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup < H) (i j : Omega) (hij : i ≠ j) (base : LeechShell 4)
    (hb : integerDot (minimumPairPlus i j).val base.val.val = 0)
    (x : LeechShell 4) (hx : integerDot (minimumPairPlus i j).val x.val.val = 0) :
    x ∈ MulAction.orbit (leechVectorStabilizer H (minimumPairPlus i j)) base :=
  orthogonal_orbit_fusion H hH.le i j hij base hb
    (strict_overgroup_orthogonal_orbit_dvd H hH
      ⟨minimumPairPlus i j,minimumPairPlus_norm i j hij⟩ base hb) x hx

theorem strict_overgroup_orthogonal_orbit_card (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup < H) (i j : Omega) (hij : i ≠ j) (base : LeechShell 4)
    (hb : integerDot (minimumPairPlus i j).val base.val.val = 0) :
    Nat.card (MulAction.orbit (leechVectorStabilizer H (minimumPairPlus i j)) base) = 93150 := by
  have he : MulAction.orbit (leechVectorStabilizer H (minimumPairPlus i j)) base =
      {x : LeechShell 4 | integerDot (minimumPairPlus i j).val x.val.val = 0} := by
    ext x
    exact ⟨orthogonal_point_orbit_orthogonal H i j base hb x,
      strict_overgroup_orthogonal_orbit_full H hH i j hij base hb x⟩
  rw [Nat.card_congr (Equiv.setCongr he)]
  exact orthogonalMinimumShell_card i j hij

end Atlas.Conway
