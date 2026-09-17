import Atlas.LinearAlgebra.QuadraticSingularPerpendicular

/-! # Hyperbolic planes in polar hyperplanes in every characteristic

For an anisotropic perpendicular vector, the selected singular vector cannot
span it. Nondegeneracy therefore supplies a partner inside its polar hyperplane;
no division by two or nondegenerate anisotropic-line splitting is needed.
-/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)

include hQ in
theorem perpendicular_hyperbolic_partner_of_not_mem_span (d a : V)
    (ha : Q a = 0) (had : Q.polarBilin a d = 0)
    (hind : a ∉ Submodule.span F {d}) :
    ∃ b, Q b = 0 ∧ Q.polarBilin a b = 1 ∧ Q.polarBilin b d = 0 := by
  have hn := polar_restriction_ne_zero Q hQ a d hind
  obtain ⟨v,hv⟩ : ∃ v : linePerp Q d, Q.polarBilin a v.val ≠ 0 := by
    by_contra! hz
    apply hn
    apply LinearMap.ext
    intro x
    exact hz x
  let c := (Q.polarBilin a v.val)⁻¹
  let w := c • v.val
  have haw : Q.polarBilin a w = 1 := by
    dsimp [w,c]
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]
  have hwd : Q.polarBilin w d = 0 := by
    change Q.polarBilin (c • v.val) d = 0
    rw [map_smul, LinearMap.smul_apply]
    have hvd : Q.polarBilin v.val d = 0 := v.prop
    rw [hvd, smul_zero]
  refine ⟨w - Q w • a, ?_, ?_, ?_⟩
  · have hqa : Q (-Q w • a) = 0 := by rw [Q.map_smul,ha,smul_zero]
    have hpa : Q.polarBilin w (-Q w • a) = -Q w := by
      calc
        Q.polarBilin w (-Q w • a) = (-Q w) • Q.polarBilin w a :=
          (Q.polarBilin w).map_smul _ _
        _ = -Q w := by rw [polar_swap Q w a,haw,smul_eq_mul,mul_one]
    have hmap := QuadraticMap.map_add Q w (-Q w • a)
    change Q (w + -Q w • a) = Q w + Q (-Q w • a) + Q.polarBilin w (-Q w • a) at hmap
    rw [hqa,hpa,add_zero,add_neg_cancel] at hmap
    simpa only [neg_smul, sub_eq_add_neg] using hmap
  · have haa : Q.polarBilin a a = 0 := by rw [polar_self,ha,mul_zero]
    calc
      Q.polarBilin a (w-Q w • a) = Q.polarBilin a w - Q w • Q.polarBilin a a :=
        (Q.polarBilin a).map_sub _ _ |>.trans (congrArg (fun z => Q.polarBilin a w-z)
          ((Q.polarBilin a).map_smul _ _))
      _ = 1 := by rw [haw,haa,smul_zero,sub_zero]
  · calc
      Q.polarBilin (w-Q w • a) d = Q.polarBilin w d - Q w • Q.polarBilin a d := by
        exact congrArg (fun z : V →ₗ[F] F => z d) ((Q.polarBilin).map_sub _ _)
          |>.trans (congrArg (fun z => Q.polarBilin w d-z)
            (congrArg (fun z : V →ₗ[F] F => z d) ((Q.polarBilin).map_smul _ _)))
      _ = 0 := by rw [hwd,had,smul_zero,sub_zero]

include hQ in
/-- Witt index at least two supplies a hyperbolic plane in every polar hyperplane,
including in characteristic two. -/
theorem hyperbolic_pair_in_perpendicular_all_char (H : WittTwoFrame Q) (d : V) :
    ∃ a b, Q a = 0 ∧ Q b = 0 ∧ Q.polarBilin a b = 1 ∧
      Q.polarBilin a d = 0 ∧ Q.polarBilin b d = 0 := by
  by_cases hd0 : d = 0
  · subst d
    exact ⟨H.e₁,H.f₁,H.qe₁,H.qf₁,H.pair₁,by simp,by simp⟩
  by_cases hqd : Q d = 0
  · have hrad : Q.radical = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      exact (Submodule.mem_bot F).mpr (hQ.1 x (fun y => LinearMap.congr_fun hx.2 y))
    obtain ⟨g,hg⟩ := exists_isometry_singular Q hrad d H.e₁ hd0
      (WittTwoFrame.first_ne_zero Q H) hqd H.qe₁
    refine ⟨g.symm H.e₂,g.symm H.f₂,(g.symm.map_app _).trans H.qe₂,
      (g.symm.map_app _).trans H.qf₂, ?_, ?_, ?_⟩
    · exact (isometry_polar Q g.symm _ _).trans H.pair₂
    · have h := isometry_polar Q g (g.symm H.e₂) d
      rw [g.apply_symm_apply,hg] at h
      exact h.symm.trans H.ee
    · have h := isometry_polar Q g (g.symm H.f₂) d
      rw [g.apply_symm_apply,hg] at h
      exact h.symm.trans H.fe
  · obtain ⟨a,hane,ha,had⟩ := isotropic_plane_perpendicular Q H.e₁ H.e₂ d
      H.qe₁ H.qe₂ ((polar_swap Q _ _).trans H.ee)
      (WittTwoFrame.first_ne_zero Q H) (WittTwoFrame.second_not_multiple Q H)
    have hind : a ∉ Submodule.span F {d} := by
      rintro hm
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
      have hc0 : c ≠ 0 := by
        intro hz
        rw [hz,zero_smul] at hc
        exact hane hc.symm
      rw [← hc,Q.map_smul,smul_eq_mul] at ha
      exact mul_ne_zero (mul_ne_zero hc0 hc0) hqd ha
    obtain ⟨b,hb,hab,hbd⟩ := perpendicular_hyperbolic_partner_of_not_mem_span Q hQ d a ha had hind
    exact ⟨a,b,ha,hb,hab,had,hbd⟩

include hQ in
/-- A singular witness for a polar functional restricted to a hyperplane,
without a characteristic assumption. -/
theorem exists_singular_perpendicular_witness_all_char (H : WittTwoFrame Q)
    (u d : V) (hu : u ∉ Submodule.span F {d}) :
    ∃ w, Q w = 0 ∧ Q.polarBilin w d = 0 ∧ Q.polarBilin u w ≠ 0 := by
  obtain ⟨a,b,ha,hb,hab,had,hbd⟩ := hyperbolic_pair_in_perpendicular_all_char Q hQ H d
  let a' : linePerp Q d := ⟨a,had⟩
  let b' : linePerp Q d := ⟨b,hbd⟩
  have hp : (linePerpForm Q d).polarBilin a' b' = 1 := by
    rw [linePerpForm_polar]
    exact hab
  obtain ⟨w,hw,hlw⟩ := exists_singular_functional_ne_zero (linePerpForm Q d) a' b'
    ha hb hp ((Q.polarBilin u).comp (linePerp Q d).subtype)
    (polar_restriction_ne_zero Q hQ u d hu)
  exact ⟨w.val,hw,w.prop,hlw⟩
end Atlas.Quadratic
