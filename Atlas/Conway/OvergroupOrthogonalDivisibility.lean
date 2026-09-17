import Atlas.Conway.OvergroupMinimumTransitivity
import Atlas.Conway.OrthogonalOddCount
import Atlas.GroupTheory.StabilizerOrbitTransport

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem leechVectorStabilizer_eq (H : Subgroup LeechIsometryGroup) (v : leech) :
    leechVectorStabilizer H v = MulAction.stabilizer H v := rfl

theorem strict_overgroup_orthogonal_orbit_dvd (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup < H) (v : LeechShell 4) (x : LeechShell 4)
    (hx : integerDot v.val.val x.val.val = 0) :
    23 ∣ Nat.card (MulAction.orbit (leechVectorStabilizer H v.val) x) := by
  let a : Omega := ((0,0),0)
  let star : LeechShell 4 := ⟨oddMinimumVector a 0,
    ((odd_minimal_shell_iff _).mpr (oddMinimumVector_mem a 0)).2.2⟩
  letI := strict_overgroup_minimum_pretransitive H hH
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H star v
  have hgv : g • star.val = v.val := congrArg Subtype.val hg
  let y : LeechShell 4 := g⁻¹ • x
  have hy : integerDot (oddProfileBase {a} ∅) y.val.val = 0 := by
    have he := g.val.prop star.val y.val
    change integerDot (g • star.val).val (g • y.val).val = _ at he
    rw [hgv] at he
    have hgy : g • y.val = x.val := by
      change (g • (g⁻¹ • x)).val = x.val
      rw [smul_inv_smul]
    rw [hgy] at he
    rw [← oddMinimumVector_zero]
    exact he.symm.trans hx
  have hd := odd_point_stabilizer_orbit_dvd H hH.le a y hy
  have hc := Nat.card_congr (Atlas.GroupTheory.stabilizerOrbitTransport g star.val y)
  have hgy : g • y = x := smul_inv_smul g x
  rw [hgv,hgy] at hc
  change 23 ∣ Nat.card (MulAction.orbit (MulAction.stabilizer H star.val) y) at hd
  change 23 ∣ Nat.card (MulAction.orbit (MulAction.stabilizer H v.val) x)
  rwa [← hc]

end Atlas.Conway
