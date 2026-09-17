import Atlas.LinearGroups.Orthogonal.SingularPrimitiveDGeometry

/-! # Singular connectors for split D in every characteristic

Common perpendicular connectors are constructed inside the actual split
hyperbolic complement. Common nonperpendicular connectors use the
characteristic-free singular witness theorem, not finite orbit tables.
-/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F : Type*} [Field F]

theorem exists_singular_nonperpendicular_connector_all_char {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (H : WittTwoFrame Q) (hQ : Q.polarBilin.Nondegenerate)
    (u v : V) (hu : u ≠ 0)
    (hv : v ∉ Submodule.span F {u}) :
    ∃ w, w ≠ 0 ∧ Q w = 0 ∧ Q.polarBilin u w ≠ 0 ∧ Q.polarBilin v w ≠ 0 := by
  obtain ⟨w, hw, hwd, huw⟩ := exists_singular_perpendicular_witness_all_char Q hQ H u (u-v)
    (not_mem_span_difference_of_independent u v hu hv)
  have hp : Q.polarBilin u w = Q.polarBilin v w := by
    rw [map_sub] at hwd
    have ht := sub_eq_zero.mp hwd
    simpa only [polar_swap Q w u, polar_swap Q w v] using ht
  refine ⟨w, ?_, hw, huw, fun h => huw (hp.trans h)⟩
  intro h
  apply huw
  rw [h, map_zero]

theorem exists_singular_perpendicular_connectorD (n : ℕ)
    (u v : VectorD (n+2) F) (hu : formD (n+2) F u = 0)
    (hv : formD (n+2) F v = 0)
    (huv : (formD (n+2) F).polarBilin u v ≠ 0) :
    ∃ w, w ≠ 0 ∧ formD (n+2) F w = 0 ∧
      (formD (n+2) F).polarBilin u w = 0 ∧
      (formD (n+2) F).polarBilin v w = 0 ∧
      w ∉ Submodule.span F {u} ∧ w ∉ Submodule.span F {v} := by
  let Q := formD (n+2) F
  let f := (Q.polarBilin u v)⁻¹ • v
  have hqv : Q v = 0 := hv
  have hquv : Q.polarBilin u v ≠ 0 := huv
  have hf : Q f = 0 := by
    simp only [f, Q.map_smul, hqv, smul_zero]
  have huf : Q.polarBilin u f = 1 := by
    simp only [f, map_smul, smul_eq_mul, inv_mul_cancel₀ hquv]
  obtain ⟨g⟩ := complement_isometryD u f hu hf huf
  let a : VectorD (n+1) F := e 0
  have ha : formD (n+1) F a = 0 := formD_e 0
  have ha0 : a ≠ 0 := by
    intro h
    have ht := congrArg (fun x : VectorD (n+1) F => x (.inl 0)) h
    exact (one_ne_zero : (1 : F) ≠ 0) (by simpa [a, e] using ht)
  let w := g.symm a
  have hw0 : w.val ≠ 0 := by
    intro h
    have hw : w = 0 := Subtype.ext h
    have ht := congrArg g hw
    have hzero : a = 0 := by simpa only [w, g.apply_symm_apply, map_zero] using ht
    exact ha0 hzero
  have hqw : Q w.val = 0 := (g.symm.map_app a).trans ha
  have hwu : Q.polarBilin w.val u = 0 := w.prop.1
  have hwf : Q.polarBilin w.val f = 0 := w.prop.2
  have hwv : Q.polarBilin w.val v = 0 := by
    change (Q.polarBilin w.val) ((Q.polarBilin u v)⁻¹ • v) = 0 at hwf
    rw [map_smul, smul_eq_mul] at hwf
    exact (mul_eq_zero.mp hwf).resolve_left (inv_ne_zero huv)
  refine ⟨w.val, hw0, hqw, (polar_swap Q u w.val).trans hwu,
    (polar_swap Q v w.val).trans hwv,
    perpendicular_not_mem_span Q u v w.val hw0 huv hwv, ?_⟩
  exact perpendicular_not_mem_span Q v u w.val hw0
    (fun h => huv ((polar_swap Q u v).trans h)) hwu

theorem singularPointsD_perpendicular_connector (n : ℕ)
    (p r : SingularPoints (formD (n+2) F))
    (hpr : ¬ SingularPerp (formD (n+2) F) p r) :
    ∃ z, z ≠ p ∧ z ≠ r ∧ SingularPerp (formD (n+2) F) p z ∧
      SingularPerp (formD (n+2) F) r z := by
  obtain ⟨w, hw, hqw, hpw, hrw, hwp, hwr⟩ := exists_singular_perpendicular_connectorD n
    p.val.rep r.val.rep p.prop r.prop hpr
  let z := singularPointMk (formD (n+2) F) w hw hqw
  refine ⟨z, singularPointMk_ne_of_not_mem_span _ p w hw hqw hwp,
    singularPointMk_ne_of_not_mem_span _ r w hw hqw hwr, ?_, ?_⟩
  · rw [← singularPointMk_rep (formD (n+2) F) p]
    exact (singularPerp_mk_iff _ p.val.rep w p.val.rep_nonzero hw p.prop hqw).mpr hpw
  · rw [← singularPointMk_rep (formD (n+2) F) r]
    exact (singularPerp_mk_iff _ r.val.rep w r.val.rep_nonzero hw r.prop hqw).mpr hrw

/-- Distinct singular points admit a singular point nonperpendicular to both,
for actual split D of rank at least two in every characteristic. -/
theorem singularPointsD_nonperpendicular_connector (n : ℕ)
    (p r : SingularPoints (formD (n+2) F)) (hpr : p ≠ r) :
    ∃ z, ¬ SingularPerp (formD (n+2) F) p z ∧
      ¬ SingularPerp (formD (n+2) F) r z := by
  obtain ⟨w, hw, hqw, hpw, hrw⟩ := exists_singular_nonperpendicular_connector_all_char
    (formD (n+2) F) (wittTwoFrameD n) polarD_nondegenerate
    p.val.rep r.val.rep p.val.rep_nonzero
    (singularPoints_rep_not_mem_span (formD (n+2) F) p r (Ne.symm hpr))
  let z := singularPointMk (formD (n+2) F) w hw hqw
  refine ⟨z, ?_, ?_⟩
  · rw [← singularPointMk_rep (formD (n+2) F) p]
    exact fun h => hpw ((singularPerp_mk_iff _ p.val.rep w p.val.rep_nonzero hw p.prop hqw).mp h)
  · rw [← singularPointMk_rep (formD (n+2) F) r]
    exact fun h => hrw ((singularPerp_mk_iff _ r.val.rep w r.val.rep_nonzero hw r.prop hqw).mp h)

end Atlas.Orthogonal
