import Atlas.LinearGroups.Orthogonal.Minus.WittFrame
import Atlas.LinearGroups.Orthogonal.Minus.StandardComplement
import Atlas.LinearGroups.Orthogonal.SingularPrimitiveDConnectors

/-! Actual minus singular-line stabilizer geometry, in every characteristic. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.Quadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem elementary_perpendicular_transport (hdeg : Module.finrank F K = 2) (n : ℕ)
    (e f x y : Vector (n+3) F K)
    (he : form hdeg (n+3) e = 0) (hf : form hdeg (n+3) f = 0)
    (hef : (form hdeg (n+3)).polarBilin e f = 1)
    (hx : form hdeg (n+3) x = 0) (hy : form hdeg (n+3) y = 0)
    (hex : (form hdeg (n+3)).polarBilin e x = 0)
    (hey : (form hdeg (n+3)).polarBilin e y = 0)
    (hxl : x ∉ Submodule.span F {e}) (hyl : y ∉ Submodule.span F {e}) :
    ∃ g : isometrySubgroup (form hdeg (n+3)), g ∈ elementarySubgroup (form hdeg (n+3)) ∧
      g.val e = e ∧ g.val x = y := by
  obtain ⟨i⟩ := complement_isometry hdeg e f he hf hef
  apply elementary_perpendicular_stabilizer_transport _ e f he hf hef
    (isometry_between_nondegenerate _ _ i (polar_nondegenerate hdeg (n+2)))
    (fun u v hu hv hqu hqv => elementary_singular_transport_of_isometry _ _ i
      (elementary_singular_transport hdeg n) u v hu hv hqu hqv)
    x y hx hy hex hey hxl hyl

theorem singular_stabilizer_perpendicular_transitive (hdeg : Module.finrank F K = 2) (n : ℕ)
    (p r s : SingularPoints (form hdeg (n+3))) (hr : r ≠ p) (hs : s ≠ p)
    (hpr : SingularPerp (form hdeg (n+3)) p r)
    (hps : SingularPerp (form hdeg (n+3)) p s) :
    ∃ g : MulAction.stabilizer (elementarySubgroup (form hdeg (n+3))) p, g • r = s := by
  obtain ⟨f, hf, hpf⟩ := exists_hyperbolic_partner hdeg (n+3) p.val.rep p.val.rep_nonzero p.prop
  obtain ⟨g, hg, hgp, hgr⟩ := elementary_perpendicular_transport hdeg n
    p.val.rep f r.val.rep s.val.rep p.prop hf hpf r.prop s.prop hpr hps
    (singularPoints_rep_not_mem_span _ p r hr) (singularPoints_rep_not_mem_span _ p s hs)
  have hfix : (⟨g, hg⟩ : elementarySubgroup (form hdeg (n+3))) • p = p :=
    singularPoints_smul_eq_of_rep _ g p p hgp
  exact ⟨⟨⟨g, hg⟩, hfix⟩, singularPoints_smul_eq_of_rep _ g r s hgr⟩

end Atlas.Orthogonal.Minus
