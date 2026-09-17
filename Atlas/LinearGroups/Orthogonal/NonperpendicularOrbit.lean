import Atlas.LinearGroups.Orthogonal.SingularOrthogonality
import Atlas.LinearGroups.Orthogonal.RootPartnerAction
import Atlas.LinearGroups.Orthogonal.RootFixedSpace

/-! # The nonperpendicular singular-point orbit of the actual root subgroup -/
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.Orthogonal
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

theorem singular_normalized_partner (e : V) (p : SingularPoints Q)
    (hp : Q.polarBilin e p.val.rep ≠ 0) :
    ∃ x : V, ∃ hx : x ≠ 0, ∃ hqx : Q x = 0,
      Q.polarBilin e x = 1 ∧ singularPointMk Q x hx hqx = p := by
  let c := (Q.polarBilin e p.val.rep)⁻¹
  have hc : c ≠ 0 := inv_ne_zero hp
  have hx : c • p.val.rep ≠ 0 := smul_ne_zero hc p.val.rep_nonzero
  have hqx : Q (c • p.val.rep) = 0 := by rw [Q.map_smul, p.prop, smul_zero]
  refine ⟨c • p.val.rep, hx, hqx, ?_, ?_⟩
  · rw [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hp
  · apply Subtype.ext
    change Projectivization.mk F (c • p.val.rep) hx = p.val
    apply Eq.trans _ (Projectivization.mk_rep p.val)
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨c, rfl⟩

theorem root_nonperpendicular_transport (e : V) (he : Q e = 0)
    (p r : SingularPoints Q) (hp : Q.polarBilin e p.val.rep ≠ 0)
    (hr : Q.polarBilin e r.val.rep ≠ 0) :
    ∃ g : isometrySubgroup Q, g ∈ rootSubgroup Q e he ∧ g • p = r := by
  obtain ⟨x, hx, hqx, hex, hxp⟩ := singular_normalized_partner Q e p hp
  obtain ⟨y, hy, hqy, hey, hyr⟩ := singular_normalized_partner Q e r hr
  obtain ⟨g, hg, _⟩ := root_unique_partner_transport Q e x he hqx hex y hqy hey
  refine ⟨g.val, g.prop, ?_⟩
  rw [← hxp, ← hyr, singularPointMk_smul]
  apply Subtype.ext
  change Projectivization.mk F (g.val.val x) _ = Projectivization.mk F y hy
  simp only [hg]

theorem singular_stabilizer_nonperpendicular_transitive (p r s : SingularPoints Q)
    (hr : ¬ SingularPerp Q p r) (hs : ¬ SingularPerp Q p s) :
    ∃ g : MulAction.stabilizer (elementarySubgroup Q) p, g • r = s := by
  obtain ⟨g, hg, hgr⟩ := root_nonperpendicular_transport Q p.val.rep p.prop r s hr hs
  have hge : g ∈ elementarySubgroup Q := rootSubgroup_le_elementary Q _ _ hg
  have hfix : (⟨g, hge⟩ : elementarySubgroup Q) • p = p := by
    apply Subtype.ext
    change g.val • p.val = p.val
    rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk]
    change Projectivization.mk F (g.val p.val.rep) _ = Projectivization.mk F p.val.rep _
    simp only [rootSubgroup_fixes_direction Q _ _ g hg, Projectivization.mk_rep]
  exact ⟨⟨⟨g, hge⟩, hfix⟩, hgr⟩
end Atlas.Orthogonal
