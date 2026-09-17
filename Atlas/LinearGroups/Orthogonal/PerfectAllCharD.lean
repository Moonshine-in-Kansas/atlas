import Mathlib.GroupTheory.IsPerfect
import Atlas.LinearGroups.Orthogonal.ScalingCommutator
import Atlas.LinearGroups.Orthogonal.RootSubgroupCoordinates
import Atlas.LinearGroups.Orthogonal.StandardComplement
import Atlas.LinearGroups.Orthogonal.WittTwoStandard
import Atlas.LinearAlgebra.QuadraticPerpendicularCharacteristicFree
import Atlas.LinearAlgebra.QuadraticComplementWitness

/-! # Elementary split-D perfectness in every characteristic

A third hyperbolic pair realizes each singular root parameter as an elementary
commutator. Hyperbolic splitting expresses every parameter as a sum of three
singular parameters. This argument includes the binary field without a torus
whose scaling factor differs from one.
-/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
open scoped commutatorElement
variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
variable (Q : QuadraticForm F V)

/-- A normalizer that translates a root parameter exhibits the translated root
as a single commutator of actual elementary elements. -/
theorem siegel_mem_commutator_of_translation (u a w : V) (hu : Q u = 0)
    (hua : Q.polarBilin u a = 0) (huw : Q.polarBilin u w = 0)
    (t : isometrySubgroup Q) (ht : t ∈ elementarySubgroup Q)
    (htu : t.val u = u) (hta : t.val a = a+w) :
    siegelElement Q u w hu huw ∈ ⁅elementarySubgroup Q,elementarySubgroup Q⁆ := by
  let r := rootParameterHom Q u hu (Multiplicative.ofAdd ⟨a,hua⟩)
  have hr : r ∈ elementarySubgroup Q := siegelElement_mem _ _ _ _ _
  have huaw : Q.polarBilin u (a+w) = 0 := by rw [map_add,hua,huw,add_zero]
  have hconj : t*r*t⁻¹ = rootParameterHom Q u hu (Multiplicative.ofAdd ⟨a+w,huaw⟩) := by
    change t*siegelElement Q u a hu hua*t⁻¹ = _
    rw [siegelElement_conj]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change siegel Q (t.val u) (t.val a) x = siegel Q u (a+w) x
    rw [htu,hta]
  have he : ⁅t,r⁆ = siegelElement Q u w hu huw := by
    rw [commutatorElement_def,hconj]
    change rootParameterHom Q u hu (Multiplicative.ofAdd ⟨a+w,huaw⟩) *
      (rootParameterHom Q u hu (Multiplicative.ofAdd ⟨a,hua⟩))⁻¹ =
      rootParameterHom Q u hu (Multiplicative.ofAdd ⟨w,huw⟩)
    rw [← map_inv,← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change (a+w)+ -a = w
    abel
  rw [← he]
  exact Subgroup.commutator_mem_commutator ht hr

/-- A hyperbolic pair perpendicular to two orthogonal singular parameters supplies
the characteristic-free root commutator relation. -/
theorem singular_siegel_mem_commutator (u w a b : V)
    (hu : Q u = 0) (hw : Q w = 0) (hb : Q b = 0)
    (huw : Q.polarBilin u w = 0) (hua : Q.polarBilin u a = 0)
    (hub : Q.polarBilin u b = 0) (hwa : Q.polarBilin w a = 0)
    (hwb : Q.polarBilin w b = 0) (hab : Q.polarBilin a b = 1) :
    siegelElement Q u w hu huw ∈ ⁅elementarySubgroup Q,elementarySubgroup Q⁆ := by
  have hbw : Q.polarBilin b (-w) = 0 := by rw [map_neg,polar_swap Q b w,hwb,neg_zero]
  let t := siegelElement Q b (-w) hb hbw
  apply siegel_mem_commutator_of_translation Q u a w hu hua huw t
    (siegelElement_mem _ _ _ _ _)
  · change siegel Q b (-w) u = u
    simp only [siegel,map_neg,huw,hub,QuadraticMap.map_neg,hw,neg_zero,
      zero_smul,mul_zero,sub_zero,add_zero]
  · have haw : Q.polarBilin a (-w) = 0 := by
      rw [map_neg,polar_swap Q a w,hwa,neg_zero]
    change siegel Q b (-w) a = a+w
    simp only [siegel,haw,hab,QuadraticMap.map_neg,hw,zero_smul,one_smul,
      mul_zero,zero_mul,sub_zero,add_zero,sub_neg_eq_add]

/-- Three singular vectors suffice to additively decompose every vector in a
quadratic space containing a hyperbolic plane. -/
theorem exists_three_singular_sum (e f : V) (he : Q e = 0) (hf : Q f = 0)
    (hef : Q.polarBilin e f = 1) (v : V) :
    ∃ x y z, Q x = 0 ∧ Q y = 0 ∧ Q z = 0 ∧ v = x+y+z := by
  let s := split Q e f he hf hef v
  let w := s.2
  refine ⟨(s.1.1-1) • e,(s.1.2+Q w.val) • f,w.val+e-Q w.val • f,
    ?_,?_,complement_singular_decomposition Q e f he hf hef w,?_⟩
  · rw [Q.map_smul,he,smul_zero]
  · rw [Q.map_smul,hf,smul_zero]
  · have hv := (split Q e f he hf hef).symm_apply_apply v
    change s.1.1 • e + s.1.2 • f + w.val = v at hv
    rw [← hv]
    module

variable [FiniteDimensional F W]

/-- The transported all-characteristic perpendicular pair in the actual complement. -/
theorem complement_perpendicular_pair_all_char (R : QuadraticForm F W)
    (e f : V) (g : (complementForm Q e f).IsometryEquiv R)
    (H : WittTwoFrame R) (hR : R.polarBilin.Nondegenerate) (v : complement Q e f) :
    ∃ a b : complement Q e f, Q a.val = 0 ∧ Q b.val = 0 ∧ Q.polarBilin a.val b.val = 1 ∧
      Q.polarBilin v.val a.val = 0 ∧ Q.polarBilin v.val b.val = 0 := by
  obtain ⟨a,b,ha,hb,hab,hav,hbv⟩ := hyperbolic_pair_in_perpendicular_all_char R hR H (g v)
  refine ⟨g.symm a,g.symm b,(g.symm.map_app a).trans ha,(g.symm.map_app b).trans hb,?_,?_,?_⟩
  · rw [← complementForm_polar Q e f]
    exact (isometry_between_polar R (complementForm Q e f) g.symm a b).trans hab
  · rw [← complementForm_polar Q e f]
    have h := isometry_between_polar (complementForm Q e f) R g v (g.symm a)
    rw [g.apply_symm_apply,polar_swap R (g v) a] at h
    exact h.symm.trans hav
  · rw [← complementForm_polar Q e f]
    have h := isometry_between_polar (complementForm Q e f) R g v (g.symm b)
    rw [g.apply_symm_apply,polar_swap R (g v) b] at h
    exact h.symm.trans hbv

/-- Every actual root in a hyperbolic pair with a two-pair standard complement
lies in the elementary commutator subgroup, in every characteristic. -/
theorem root_mem_commutator_all_char (e f : V) (he : Q e = 0)
    (R : QuadraticForm F W) (g : (complementForm Q e f).IsometryEquiv R)
    (H : WittTwoFrame R) (hR : R.polarBilin.Nondegenerate) (w : complement Q e f) :
    rootComplementHom Q e f he (Multiplicative.ofAdd w) ∈
      ⁅elementarySubgroup Q,elementarySubgroup Q⁆ := by
  have hs : ∀ v : complement Q e f, Q v.val = 0 →
      rootComplementHom Q e f he (Multiplicative.ofAdd v) ∈
        ⁅elementarySubgroup Q,elementarySubgroup Q⁆ := by
    intro v hv
    obtain ⟨a,b,ha,hb,hab,hva,hvb⟩ := complement_perpendicular_pair_all_char Q R e f g H hR v
    exact singular_siegel_mem_commutator Q e v.val a.val b.val he hv hb
      ((polar_swap Q e v.val).trans v.prop.1)
      ((polar_swap Q e a.val).trans a.prop.1)
      ((polar_swap Q e b.val).trans b.prop.1) hva hvb hab
  obtain ⟨x,y,z,hx,hy,hz,hw⟩ := exists_three_singular_sum R H.e₁ H.f₁ H.qe₁ H.qf₁ H.pair₁ (g w)
  have hw' : w = g.symm x+g.symm y+g.symm z := by
    apply g.injective
    change g w = g (g.symm x+g.symm y+g.symm z)
    rw [map_add,map_add,g.apply_symm_apply,g.apply_symm_apply,g.apply_symm_apply]
    exact hw
  rw [hw']
  have hm : Multiplicative.ofAdd (g.symm x+g.symm y+g.symm z) =
      Multiplicative.ofAdd (g.symm x)*Multiplicative.ofAdd (g.symm y)*Multiplicative.ofAdd (g.symm z) := rfl
  rw [hm,map_mul,map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (hs _ ((g.symm.map_app x).trans hx)) (hs _ ((g.symm.map_app y).trans hy)))
    (hs _ ((g.symm.map_app z).trans hz))

variable [FiniteDimensional F V]

/-- Intrinsic perfectness from actual two-pair complement isometries, without
any field-size or characteristic restriction. -/
theorem elementary_perfect_of_complements_all_char
    (hQ : Q.polarBilin.Nondegenerate) (R : QuadraticForm F W)
    (H : WittTwoFrame R) (hR : R.polarBilin.Nondegenerate)
    (hc : ∀ e f, Q e = 0 → Q f = 0 → Q.polarBilin e f = 1 →
      Nonempty ((complementForm Q e f).IsometryEquiv R)) :
    Group.IsPerfect (elementarySubgroup Q) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_left _ _) _
  apply (Subgroup.closure_le _).mpr
  rintro s ⟨u,v,hu,huv,rfl⟩
  by_cases hun : u = 0
  · subst u
    have hs : siegelElement Q 0 v hu huv = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change siegel Q 0 v x = x
      simp [siegel]
    rw [hs]
    exact Subgroup.one_mem _
  · obtain ⟨f,hf,huf⟩ := exists_hyperbolic_partner Q u hu (fun h => hun (hQ.1 u h))
    obtain ⟨g⟩ := hc u f hu hf huf
    let w := rootPerpendicularRepresentative Q u f hu huf ⟨v,huv⟩
    have he := rootPerpendicularRepresentative_element Q u f hu huf ⟨v,huv⟩
    change rootComplementHom Q u f hu (Multiplicative.ofAdd w) = siegelElement Q u v hu huv at he
    rw [← he]
    exact root_mem_commutator_all_char Q u f hu R g H hR w

/-- Perfectness of the actual elementary split-D group in rank at least three,
over every field, including the binary field. -/
theorem elementaryD_perfect_all_char (n : ℕ) :
    Group.IsPerfect (elementarySubgroup (formD (n + 3) F)) :=
  elementary_perfect_of_complements_all_char _ polarD_nondegenerate (formD (n + 2) F)
    (wittTwoFrameD n) polarD_nondegenerate
    (fun e f he hf hef => complement_isometryD e f he hf hef)

end Atlas.Orthogonal
