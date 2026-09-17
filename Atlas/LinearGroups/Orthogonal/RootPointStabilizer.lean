import Atlas.LinearGroups.Orthogonal.NonperpendicularOrbit
import Atlas.LinearGroups.Orthogonal.RootSubgroupConjugation

/-! # The actual abelian root subgroup is normal in its singular-point stabilizer -/
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.Orthogonal
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (p : SingularPoints Q)

theorem elementaryRoot_le_point_stabilizer :
    (rootSubgroup Q p.val.rep p.prop).subgroupOf (elementarySubgroup Q) ≤
      MulAction.stabilizer (elementarySubgroup Q) p := by
  intro g hg
  change g • p = p
  apply Subtype.ext
  change g.val.val • p.val = p.val
  rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk]
  change Projectivization.mk F (g.val.val p.val.rep) _ = Projectivization.mk F p.val.rep _
  simp only [rootSubgroup_fixes_direction Q _ _ g.val hg]

theorem elementaryRoot_normal_point_stabilizer :
    (((rootSubgroup Q p.val.rep p.prop).subgroupOf (elementarySubgroup Q)).subgroupOf
      (MulAction.stabilizer (elementarySubgroup Q) p)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff (elementaryRoot_le_point_stabilizer Q p)).mpr
  intro r g hr hg
  have h : g.val.val • p.val = p.val := congrArg Subtype.val hg
  rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨c, hc⟩ := h
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hc
    exact p.val.rep_nonzero (g.val.val.injective (hc.symm.trans (map_zero _).symm))
  have hn := line_stabilizer_normalizes_root Q p.val.rep p.prop g.val c hc0 hc.symm
  exact (Subgroup.mem_normalizer_iff.mp hn r.val).mp hr
end Atlas.Orthogonal
