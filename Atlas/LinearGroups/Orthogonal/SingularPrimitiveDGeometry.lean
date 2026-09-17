import Atlas.LinearGroups.Orthogonal.SingularPointConnectors
import Atlas.LinearGroups.Orthogonal.ElementaryTransitivityAllChar

/-! # Characteristic-free singular-line geometry for actual split D -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F : Type*} [Field F]

theorem elementaryD_perpendicular_stabilizer_transport (n : ℕ)
    (e f x y : VectorD (n+3) F)
    (he : formD (n+3) F e = 0) (hf : formD (n+3) F f = 0)
    (hef : (formD (n+3) F).polarBilin e f = 1)
    (hx : formD (n+3) F x = 0) (hy : formD (n+3) F y = 0)
    (hex : (formD (n+3) F).polarBilin e x = 0)
    (hey : (formD (n+3) F).polarBilin e y = 0)
    (hxl : x ∉ Submodule.span F {e}) (hyl : y ∉ Submodule.span F {e}) :
    ∃ g : isometrySubgroup (formD (n+3) F), g ∈ elementarySubgroup (formD (n+3) F) ∧
      g.val e = e ∧ g.val x = y := by
  obtain ⟨i⟩ := complement_isometryD e f he hf hef
  apply elementary_perpendicular_stabilizer_transport _ e f he hf hef
    (isometry_between_nondegenerate _ _ i polarD_nondegenerate)
    (fun u v hu hv hqu hqv => elementary_singular_transport_of_isometry _ _ i
      (elementaryD_singular_transport_all_char n) u v hu hv hqu hqv)
    x y hx hy hex hey hxl hyl

theorem singular_stabilizerD_perpendicular_transitive (n : ℕ)
    (p r s : SingularPoints (formD (n+3) F)) (hr : r ≠ p) (hs : s ≠ p)
    (hpr : SingularPerp (formD (n+3) F) p r)
    (hps : SingularPerp (formD (n+3) F) p s) :
    ∃ g : MulAction.stabilizer (elementarySubgroup (formD (n+3) F)) p, g • r = s := by
  obtain ⟨f, hf, hpf⟩ := exists_hyperbolic_partnerD p.val.rep p.val.rep_nonzero p.prop
  obtain ⟨g, hg, hgp, hgr⟩ := elementaryD_perpendicular_stabilizer_transport n
    p.val.rep f r.val.rep s.val.rep p.prop hf hpf r.prop s.prop hpr hps
    (singularPoints_rep_not_mem_span _ p r hr) (singularPoints_rep_not_mem_span _ p s hs)
  have hfix : (⟨g, hg⟩ : elementarySubgroup (formD (n+3) F)) • p = p :=
    singularPoints_smul_eq_of_rep _ g p p hgp
  exact ⟨⟨⟨g, hg⟩, hfix⟩, singularPoints_smul_eq_of_rep _ g r s hgr⟩

end Atlas.Orthogonal
