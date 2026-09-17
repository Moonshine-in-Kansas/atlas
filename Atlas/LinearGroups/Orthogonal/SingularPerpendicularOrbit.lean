import Atlas.LinearGroups.Orthogonal.PerpendicularStabilizerOrbit
import Atlas.LinearGroups.Orthogonal.SingularOrthogonality

/-! # The perpendicular singular-point orbit of an elementary point stabilizer -/
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.Orthogonal
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- Representatives of distinct singular points lie outside each other's lines. -/
theorem singularPoints_rep_not_mem_span (p r : SingularPoints Q) (hne : r ≠ p) :
    r.val.rep ∉ Submodule.span F {p.val.rep} := by
  intro h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  apply hne
  apply Subtype.ext
  rw [← Projectivization.mk_rep r.val, ← Projectivization.mk_rep p.val,
    Projectivization.mk_eq_mk_iff']
  exact ⟨c, hc⟩

/-- Equality of actual representative images gives equality of singular points. -/
theorem singularPoints_smul_eq_of_rep (g : isometrySubgroup Q) (p r : SingularPoints Q)
    (h : g.val p.val.rep = r.val.rep) : g • p = r := by
  apply Subtype.ext
  change g.val • p.val = r.val
  rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk]
  change Projectivization.mk F (g.val p.val.rep) _ = r.val
  simp only [h, Projectivization.mk_rep]

/-- The actual elementary point stabilizer in odd B of rank at least three is
transitive on the other perpendicular singular points. -/
theorem singular_stabilizerB_perpendicular_transitive (n : ℕ) (h2 : (2 : F) ≠ 0)
    (p r s : SingularPoints (formB (n+3) F)) (hr : r ≠ p) (hs : s ≠ p)
    (hpr : SingularPerp (formB (n+3) F) p r)
    (hps : SingularPerp (formB (n+3) F) p s) :
    ∃ g : MulAction.stabilizer (elementarySubgroup (formB (n+3) F)) p, g • r = s := by
  obtain ⟨f, hf, hpf⟩ := exists_hyperbolic_partnerB p.val.rep p.val.rep_nonzero p.prop
  obtain ⟨g, hg, hgp, hgr⟩ := elementaryB_perpendicular_stabilizer_transport n h2
    p.val.rep f r.val.rep s.val.rep p.prop hf hpf r.prop s.prop hpr hps
    (singularPoints_rep_not_mem_span _ p r hr) (singularPoints_rep_not_mem_span _ p s hs)
  have hfix : (⟨g, hg⟩ : elementarySubgroup (formB (n+3) F)) • p = p :=
    singularPoints_smul_eq_of_rep _ g p p hgp
  exact ⟨⟨⟨g, hg⟩, hfix⟩, singularPoints_smul_eq_of_rep _ g r s hgr⟩

end Atlas.Orthogonal
