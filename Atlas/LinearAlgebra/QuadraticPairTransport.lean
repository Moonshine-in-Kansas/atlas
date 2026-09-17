import Atlas.LinearAlgebra.QuadraticTransitivity
import Atlas.LinearAlgebra.QuadraticSplit
import Atlas.LinearAlgebra.QuadraticSiegel

/-! # Extension of ordered quadratic hyperbolic pairs by actual isometries -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- The Siegel subgroup fixing e transports its singular normalized partners. -/
theorem exists_isometry_fixing_first (e f v : V) (he : Q e=0) (hf : Q f=0)
    (hv : Q v=0) (hef : Q.polarBilin e f=1) (hev : Q.polarBilin e v=1) :
    ∃ k : Q.IsometryEquiv Q, k e=e ∧ k f=v := by
  let s := split Q e f he hf hef
  let w := (s v).2
  have hw := (mem_complement Q e f w.val).mp w.prop
  have hew : Q.polarBilin e w.val=0 := (polar_swap Q e w.val).trans hw.1
  have hfw : Q.polarBilin f w.val=0 := (polar_swap Q f w.val).trans hw.2
  have hve : Q.polarBilin v e=1 := (polar_swap Q v e).trans hev
  have hfe : Q.polarBilin f e=1 := (polar_swap Q f e).trans hef
  have ha : Q.polarBilin v f = -Q w.val := by
    have h := form_split Q e f he hf hef v
    change Q v=Q.polarBilin v f * Q.polarBilin v e+Q w.val at h
    rw [hv,hve,mul_one] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hn : Q.polarBilin e (-w.val)=0 := by rw [map_neg,hew,neg_zero]
  refine ⟨siegelIsometry Q e (-w.val) he hn,siegel_fix Q e (-w.val) he hn,?_⟩
  have hd := s.symm_apply_apply v
  change Q.polarBilin v f • e+Q.polarBilin v e • f+w.val=v at hd
  rw [ha,hve,one_smul] at hd
  change siegel Q e (-w.val) f=v
  rw [← hd]
  simp only [siegel,map_neg,hfw,hfe,Q.map_neg,neg_zero,zero_smul,one_smul,mul_one]
  module

/-- Any two ordered hyperbolic pairs extend to a full quadratic isometry. -/
theorem exists_isometry_hyperbolic_pair (hQ : Q.radical=⊥) (e f u v : V)
    (he : Q e=0) (hf : Q f=0) (hu : Q u=0) (hv : Q v=0)
    (hef : Q.polarBilin e f=1) (huv : Q.polarBilin u v=1) :
    ∃ g : Q.IsometryEquiv Q, g e=u ∧ g f=v := by
  have hne : e≠0 := by
    intro h; subst e
    simpa only [map_zero,LinearMap.zero_apply,zero_ne_one] using hef
  have hnu : u≠0 := by
    intro h; subst u
    simpa only [map_zero,LinearMap.zero_apply,zero_ne_one] using huv
  obtain ⟨g,hg⟩ := exists_isometry_singular Q hQ e u hne hnu he hu
  have hgf : Q (g f)=0 := (g.map_app f).trans hf
  have hugf : Q.polarBilin u (g f)=1 := by
    rw [← hg,isometry_polar,hef]
  obtain ⟨k,hku,hkf⟩ := exists_isometry_fixing_first Q u (g f) v hu hgf hv hugf huv
  refine ⟨g.trans k,?_,?_⟩
  · change k (g e)=u
    rw [hg,hku]
  · exact hkf

end Atlas.Quadratic
