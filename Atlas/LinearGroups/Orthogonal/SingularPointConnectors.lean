import Atlas.LinearGroups.Orthogonal.SingularConnectors
import Atlas.LinearGroups.Orthogonal.SingularPerpendicularOrbit

/-! # Connectors on the actual singular projective points of B -/
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.Orthogonal
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- A vector outside a projective point's line defines a different singular point. -/
theorem singularPointMk_ne_of_not_mem_span (Q : QuadraticForm F V)
    (p : SingularPoints Q) (w : V) (hw : w ≠ 0) (hqw : Q w = 0)
    (hwp : w ∉ Submodule.span F {p.val.rep}) : singularPointMk Q w hw hqw ≠ p := by
  intro h
  have he := congrArg Subtype.val h
  change Projectivization.mk F w hw = p.val at he
  rw [← Projectivization.mk_rep p.val] at he
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' F w p.val.rep hw p.val.rep_nonzero).mp he
  exact hwp (Submodule.mem_span_singleton.mpr ⟨c, hc⟩)

/-- Nonperpendicular singular points admit a third point perpendicular to both,
for actual B of rank at least two, in every characteristic. -/
theorem singularPointsB_perpendicular_connector (n : ℕ)
    (p r : SingularPoints (formB (n+2) F))
    (hpr : ¬ SingularPerp (formB (n+2) F) p r) :
    ∃ z, z ≠ p ∧ z ≠ r ∧ SingularPerp (formB (n+2) F) p z ∧
      SingularPerp (formB (n+2) F) r z := by
  obtain ⟨w, hw, hqw, hpw, hrw, hwp, hwr⟩ := exists_singular_perpendicular_connectorB n
    p.val.rep r.val.rep p.prop r.prop hpr
  let z := singularPointMk (formB (n+2) F) w hw hqw
  refine ⟨z, singularPointMk_ne_of_not_mem_span _ p w hw hqw hwp,
    singularPointMk_ne_of_not_mem_span _ r w hw hqw hwr, ?_, ?_⟩
  · rw [← singularPointMk_rep (formB (n+2) F) p]
    exact (singularPerp_mk_iff _ p.val.rep w p.val.rep_nonzero hw p.prop hqw).mpr hpw
  · rw [← singularPointMk_rep (formB (n+2) F) r]
    exact (singularPerp_mk_iff _ r.val.rep w r.val.rep_nonzero hw r.prop hqw).mpr hrw

/-- Distinct singular points admit a singular point nonperpendicular to both,
for actual odd-characteristic B of rank at least two. -/
theorem singularPointsB_nonperpendicular_connector (n : ℕ) (h2 : (2 : F) ≠ 0)
    (p r : SingularPoints (formB (n+2) F)) (hpr : p ≠ r) :
    ∃ z, ¬ SingularPerp (formB (n+2) F) p z ∧
      ¬ SingularPerp (formB (n+2) F) r z := by
  obtain ⟨w, hw, hqw, hpw, hrw⟩ := exists_singular_nonperpendicular_connector
    (formB (n+2) F) (wittTwoFrameB n) (polarB_nondegenerate h2) h2
    p.val.rep r.val.rep p.val.rep_nonzero
    (singularPoints_rep_not_mem_span (formB (n+2) F) p r (Ne.symm hpr))
  let z := singularPointMk (formB (n+2) F) w hw hqw
  refine ⟨z, ?_, ?_⟩
  · rw [← singularPointMk_rep (formB (n+2) F) p]
    exact fun h => hpw ((singularPerp_mk_iff _ p.val.rep w p.val.rep_nonzero hw p.prop hqw).mp h)
  · rw [← singularPointMk_rep (formB (n+2) F) r]
    exact fun h => hrw ((singularPerp_mk_iff _ r.val.rep w r.val.rep_nonzero hw r.prop hqw).mp h)
end Atlas.Orthogonal
