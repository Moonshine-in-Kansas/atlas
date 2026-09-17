import Atlas.LinearGroups.Orthogonal.RootFixedSpace
import Atlas.LinearAlgebra.QuadraticPerpendicularCharacteristicFree
import Atlas.LinearGroups.Orthogonal.ElementaryTransitivity
import Atlas.LinearGroups.Orthogonal.RootPartnerAction
import Atlas.LinearGroups.Orthogonal.WittTwoStandard

/-! # Characteristic-free elementary transport in Witt index at least two

Transport is obtained directly from singular directions and the actual root
subgroups; no reflection-generation theorem or elementary quotient is used.
-/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (H : WittTwoFrame Q)
  (hQ : Q.polarBilin.Nondegenerate)

private theorem independent_difference (u v : V) (hu : u ≠ 0)
    (hv : v ∉ Submodule.span F {u}) : u ∉ Submodule.span F {u-v} := by
  intro h
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0,zero_smul] at hc
    exact hu hc.symm
  have hs : u-v = c⁻¹ • u := by
    have ht := congrArg (fun x : V => c⁻¹ • x) hc
    simpa only [smul_smul,inv_mul_cancel₀ hc0,one_smul] using ht
  apply hv
  apply Submodule.mem_span_singleton.mpr
  refine ⟨1-c⁻¹, ?_⟩
  rw [sub_smul,one_smul,← hs]
  abel

include H hQ in
theorem elementary_transport_independent_all_char (u v : V) (hu : u ≠ 0)
    (hind : v ∉ Submodule.span F {u}) (hval : Q u = Q v) :
    ∃ g : isometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val u = v := by
  obtain ⟨w,hw,hwd,huw⟩ := exists_singular_perpendicular_witness_all_char Q hQ H u (u-v)
    (independent_difference u v hu hind)
  have hp : Q.polarBilin u w = Q.polarBilin v w := by
    rw [map_sub] at hwd
    have ht := sub_eq_zero.mp hwd
    simpa only [polar_swap Q w u,polar_swap Q w v] using ht
  exact elementary_transport_with_direction Q u v w hw hval hp huw

private theorem singular_nonperpendicular_not_span (u v : V) (hu : Q u = 0)
    (huv : Q.polarBilin u v ≠ 0) : v ∉ Submodule.span F {u} := by
  intro hm
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
  apply huv
  rw [← hc, map_smul, polar_self, hu, mul_zero, smul_zero]

include H hQ in
/-- Actual elementary transitivity on all nonzero singular vectors in every characteristic. -/
theorem elementary_singular_transport_all_char (u v : V) (hu : u ≠ 0) (hv : v ≠ 0)
    (hqu : Q u = 0) (hqv : Q v = 0) :
    ∃ g : isometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val u = v := by
  classical
  by_cases hind : v ∈ Submodule.span F {u}
  · have hl : Q.polarBilin u ≠ 0 := by
      intro hl
      apply hu
      apply hQ.1
      intro x
      exact LinearMap.congr_fun hl x
    obtain ⟨w,hqw,huw⟩ := exists_singular_functional_ne_zero Q H.e₁ H.f₁
      H.qe₁ H.qf₁ H.pair₁ (Q.polarBilin u) hl
    have hw : w ≠ 0 := by intro hz; exact huw (by rw [hz,map_zero])
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hind
    have hc0 : c ≠ 0 := by intro hz; apply hv; rw [← hc,hz,zero_smul]
    have hvw : Q.polarBilin v w ≠ 0 := by
      rw [← hc,map_smul,LinearMap.smul_apply,smul_eq_mul]
      exact mul_ne_zero hc0 huw
    obtain ⟨g,hg,hgu⟩ := elementary_transport_independent_all_char Q H hQ u w hu
      (singular_nonperpendicular_not_span Q u w hqu huw) (hqu.trans hqw.symm)
    obtain ⟨k,hk,hkw⟩ := elementary_transport_independent_all_char Q H hQ w v hw
      (singular_nonperpendicular_not_span Q w v hqw (by rwa [polar_swap])) (hqw.trans hqv.symm)
    refine ⟨k*g,(elementarySubgroup Q).mul_mem hk hg, ?_⟩
    change k.val (g.val u) = v
    rw [hgu,hkw]
  · exact elementary_transport_independent_all_char Q H hQ u v hu hind (hqu.trans hqv.symm)

include H hQ in
/-- After singular-vector transport, the actual root group corrects the partner. -/
theorem elementary_pair_transport_all_char (e f u v : V)
    (he : Q e = 0) (hf : Q f = 0) (hu : Q u = 0) (hv : Q v = 0)
    (hef : Q.polarBilin e f = 1) (huv : Q.polarBilin u v = 1) :
    ∃ g : isometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val e = u ∧ g.val f = v := by
  have hene : e ≠ 0 := by
    intro hz
    rw [hz,map_zero,LinearMap.zero_apply] at hef
    exact zero_ne_one hef
  have hune : u ≠ 0 := by
    intro hz
    rw [hz,map_zero,LinearMap.zero_apply] at huv
    exact zero_ne_one huv
  obtain ⟨g,hg,hge⟩ := elementary_singular_transport_all_char Q H hQ e u hene hune he hu
  have hgf : Q (g.val f) = 0 := (g.prop f).trans hf
  have hpair : Q.polarBilin u (g.val f) = 1 := by
    have hp := isometry_polar Q (isometryCarrierEquiv Q g) e f
    change Q.polarBilin (g.val e) (g.val f) = Q.polarBilin e f at hp
    rw [hge,hef] at hp
    exact hp
  obtain ⟨r,hr,_⟩ := root_unique_partner_transport Q u (g.val f) hu hgf hpair v hv huv
  refine ⟨r.val*g,(elementarySubgroup Q).mul_mem
    (rootSubgroup_le_elementary Q u hu r.prop) hg, ?_, ?_⟩
  · change r.val.val (g.val e) = u
    rw [hge]
    exact rootSubgroup_fixes_direction Q u hu r.val r.prop
  · exact hr

/-- The actual split D singular-vector orbit in rank at least two, including even fields. -/
theorem elementaryD_singular_transport_all_char (n : ℕ)
    (u v : VectorD (n+2) F) (hu : u ≠ 0) (hv : v ≠ 0)
    (hqu : formD (n+2) F u = 0) (hqv : formD (n+2) F v = 0) :
    ∃ g : O_DPlus (n+2) F, g ∈ elementarySubgroup (formD (n+2) F) ∧ g.val u = v :=
  elementary_singular_transport_all_char _ (wittTwoFrameD n) polarD_nondegenerate u v hu hv hqu hqv

/-- The actual split D hyperbolic-pair orbit in rank at least two, in every characteristic. -/
theorem elementaryD_pair_transport_all_char (n : ℕ)
    (e f u v : VectorD (n+2) F)
    (he : formD (n+2) F e = 0) (hf : formD (n+2) F f = 0)
    (hu : formD (n+2) F u = 0) (hv : formD (n+2) F v = 0)
    (hef : (formD (n+2) F).polarBilin e f = 1)
    (huv : (formD (n+2) F).polarBilin u v = 1) :
    ∃ g : O_DPlus (n+2) F, g ∈ elementarySubgroup (formD (n+2) F) ∧
      g.val e = u ∧ g.val f = v :=
  elementary_pair_transport_all_char _ (wittTwoFrameD n) polarD_nondegenerate e f u v
    he hf hu hv hef huv
end Atlas.Orthogonal
