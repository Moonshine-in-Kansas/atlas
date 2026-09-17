import Atlas.LinearGroups.Orthogonal.ReflectionGroup

/-! # Full quadratic reflection generation in odd characteristic -/
noncomputable section
universe u v
namespace Atlas.Orthogonal
open Atlas.Quadratic

/-- Dimension induction uses actual nondegenerate-line restriction and reflection extension. -/
theorem reflection_generation_dim (F : Type u) [Field F] (h2 : (2 : F) ≠ 0) (d : ℕ) :
    ∀ (W : Type v) [AddCommGroup W] [Module F W] [FiniteDimensional F W],
      Module.finrank F W = d → ∀ (Q : QuadraticForm F W), Q.polarBilin.Nondegenerate →
        reflectionSubgroup Q = ⊤ := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro W _ _ _ hd Q hQ
    by_cases hz : d = 0
    · haveI : Subsingleton W := Module.finrank_zero_iff.mp (hd.trans hz)
      apply top_unique
      intro g _
      have hg : g = 1 := Subtype.ext (Subsingleton.elim _ _)
      rw [hg]
      exact (reflectionSubgroup Q).one_mem
    · haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (M := W) (by omega)
      obtain ⟨x, hx⟩ := exists_ne (0 : W)
      have hex : ∃ a : W, Q a ≠ 0 := by
        by_contra! hzero
        apply hx
        apply hQ.1
        intro y
        simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hzero, sub_zero]
      obtain ⟨a, hqa⟩ := hex
      have haa : Q.polarBilin a a ≠ 0 := by rw [polar_self]; exact mul_ne_zero h2 hqa
      have hdim := linePerp_finrank Q a haa
      have hlt : Module.finrank F (linePerp Q a) < d := by omega
      have hgen := ih (Module.finrank F (linePerp Q a)) hlt (linePerp Q a) rfl
        (linePerpForm Q a) (linePerpForm_nondegenerate Q a haa hQ)
      apply top_unique
      intro g _
      have hga : Q (g.val a) ≠ 0 := by rw [g.prop]; exact hqa
      obtain ⟨r, hr, hrg⟩ := reflectionSubgroup_transport Q h2 (g.val a) a hga (g.prop a)
      let k := r*g
      have hkfix : (isometryCarrierEquiv Q k) a = a := hrg
      let kc := (isometryCarrierEquiv (linePerpForm Q a)).symm
        (lineRestriction Q a (isometryCarrierEquiv Q k) hkfix)
      have hkc : kc ∈ reflectionSubgroup (linePerpForm Q a) := by rw [hgen]; trivial
      have he : lineExtensionHom Q a haa kc = k := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro y
        exact congrArg (fun t : Q.IsometryEquiv Q => t y)
          (lineExtension_restriction Q a haa (isometryCarrierEquiv Q k) hkfix)
      have hk := lineExtensionHom_mem Q a haa kc hkc
      rw [he] at hk
      have hg := (reflectionSubgroup Q).mul_mem ((reflectionSubgroup Q).inv_mem hr) hk
      change r⁻¹ * (r*g) ∈ reflectionSubgroup Q at hg
      simpa only [inv_mul_cancel_left] using hg

/-- Cartan–Dieudonné generation for the actual full quadratic-isometry carrier. -/
theorem reflectionSubgroup_eq_top {F : Type u} [Field F] {V : Type v}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0) :
    reflectionSubgroup Q = ⊤ :=
  reflection_generation_dim F h2 (Module.finrank F V) V rfl Q hQ

end Atlas.Orthogonal
