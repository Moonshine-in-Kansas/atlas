import Atlas.LinearGroups.Orthogonal.PerpendicularLineStabilizerOrbit
import Atlas.LinearGroups.Orthogonal.B1ConjugationImage
import Atlas.LinearGroups.Orthogonal.SingularPrimitiveB

noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F : Type*} [Field F]

theorem elementaryB1_singular_line_transport (u v : VectorB 1 F)
    (hu : u≠0) (hv : v≠0) (hqu : formB 1 F u=0) (hqv : formB 1 F v=0) :
    ∃g : O_B 1 F,g∈elementarySubgroup (formB 1 F) ∧ ∃c : F,c≠0 ∧ g.val u=c • v := by
  obtain ⟨a,c,hc,ha⟩ := B1Conjugation.singular_line_orbit u hu hqu
  obtain ⟨b,d,hd,hb⟩ := B1Conjugation.singular_line_orbit v hv hqv
  let ga := B1Conjugation.toOrthogonal a
  let gb := B1Conjugation.toOrthogonal b
  have hgb : gb.val (e 0,0)=d⁻¹ • v := by
    rw [hb,smul_smul,inv_mul_cancel₀ hd,one_smul]
  refine ⟨gb*ga⁻¹,(elementarySubgroup _).mul_mem
    (B1Conjugation.toOrthogonal_mem_elementary b)
    ((elementarySubgroup _).inv_mem (B1Conjugation.toOrthogonal_mem_elementary a)),
    c*d⁻¹,mul_ne_zero hc (inv_ne_zero hd),?_⟩
  change gb.val (ga.val.symm u)=(c*d⁻¹) • v
  rw [ha,map_smul,LinearEquiv.symm_apply_apply,map_smul,hgb,smul_smul]

theorem elementaryB2_perpendicular_stabilizer_line_transport (h2 : (2:F)≠0)
    (e f x y : VectorB 2 F) (he : formB 2 F e=0) (hf : formB 2 F f=0)
    (hef : (formB 2 F).polarBilin e f=1) (hx : formB 2 F x=0) (hy : formB 2 F y=0)
    (hex : (formB 2 F).polarBilin e x=0) (hey : (formB 2 F).polarBilin e y=0)
    (hxl : x∉Submodule.span F {e}) (hyl : y∉Submodule.span F {e}) :
    ∃g : O_B 2 F,g∈elementarySubgroup (formB 2 F) ∧ g.val e=e ∧
      ∃c : F,c≠0 ∧ g.val x=c • y := by
  obtain ⟨i⟩ := complement_isometryB (n := 1) e f he hf hef
  apply elementary_perpendicular_stabilizer_line_transport _ e f he hf hef
    (isometry_between_nondegenerate _ _ i (polarB_nondegenerate h2))
    (fun u v hu hv hqu hqv => elementary_singular_line_transport_of_isometry _ _ i
      elementaryB1_singular_line_transport u v hu hv hqu hqv)
    x y hx hy hex hey hxl hyl

theorem singularPoints_smul_eq_of_scaled_rep {V : Type*} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (g : isometrySubgroup Q) (p r : SingularPoints Q)
    (c : F) (h : g.val p.val.rep=c • r.val.rep) : g • p=r := by
  apply Subtype.ext
  change g.val • p.val=r.val
  rw [←Projectivization.mk_rep p.val,Projectivization.smul_mk,←Projectivization.mk_rep r.val,
    Projectivization.mk_eq_mk_iff']
  exact ⟨c,h.symm⟩

theorem singular_stabilizerB2_perpendicular_transitive (h2 : (2:F)≠0)
    (p r s : SingularPoints (formB 2 F)) (hr : r≠p) (hs : s≠p)
    (hpr : SingularPerp (formB 2 F) p r) (hps : SingularPerp (formB 2 F) p s) :
    ∃g : MulAction.stabilizer (elementarySubgroup (formB 2 F)) p,g • r=s := by
  obtain ⟨f,hf,hpf⟩ := exists_hyperbolic_partnerB p.val.rep p.val.rep_nonzero p.prop
  obtain ⟨g,hg,hgp,c,hc,hgr⟩ := elementaryB2_perpendicular_stabilizer_line_transport h2
    p.val.rep f r.val.rep s.val.rep p.prop hf hpf r.prop s.prop hpr hps
    (singularPoints_rep_not_mem_span _ p r hr) (singularPoints_rep_not_mem_span _ p s hs)
  have hfix : (⟨g,hg⟩ : elementarySubgroup (formB 2 F)) • p=p :=
    singularPoints_smul_eq_of_rep _ g p p hgp
  exact ⟨⟨⟨g,hg⟩,hfix⟩,singularPoints_smul_eq_of_scaled_rep _ g r s c hgr⟩

theorem singularPointsB2_primitive (h2 : (2:F)≠0) :
    MulAction.IsPreprimitive (elementarySubgroup (formB 2 F)) (SingularPoints (formB 2 F)) := by
  letI := singularPointsB_pretransitive 0 h2
  let Q := formB 2 F
  let a := singularPointMk Q (wittTwoFrameB 0).e₁
    (WittTwoFrame.first_ne_zero Q (wittTwoFrameB 0)) (wittTwoFrameB 0).qe₁
  apply Atlas.GroupTheory.primitive_of_two_suborbits_and_connectors a
    (SingularPerp Q) (singularPerp_symmetric Q)
    (singular_stabilizerB2_perpendicular_transitive h2)
    (singular_stabilizer_nonperpendicular_transitive Q)
  · intro p r _ hpr
    exact singularPointsB_perpendicular_connector 0 p r hpr
  · intro p r hpr _
    exact singularPointsB_nonperpendicular_connector 0 h2 p r hpr

end Atlas.Orthogonal
