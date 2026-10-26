import Atlas.LinearGroups.Orthogonal.Minus.SingularGeometry
import Atlas.LinearGroups.Orthogonal.SingularPrimitiveDConnectors

/-! Actual minus singular-line stabilizer geometry, in every characteristic. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.Quadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem exists_singular_perpendicular_connector (hdeg : Module.finrank F K = 2) (n : ℕ)
    (u v : Vector (n+2) F K) (hu : form hdeg (n+2) u = 0)
    (hv : form hdeg (n+2) v = 0)
    (huv : (form hdeg (n+2)).polarBilin u v ≠ 0) :
    ∃ w, w ≠ 0 ∧ form hdeg (n+2) w = 0 ∧
      (form hdeg (n+2)).polarBilin u w = 0 ∧
      (form hdeg (n+2)).polarBilin v w = 0 ∧
      w ∉ Submodule.span F {u} ∧ w ∉ Submodule.span F {v} := by
  let Q := form hdeg (n+2)
  let f := (Q.polarBilin u v)⁻¹ • v
  have hqv : Q v = 0 := hv
  have hquv : Q.polarBilin u v ≠ 0 := huv
  have hf : Q f = 0 := by
    simp only [f, Q.map_smul, hqv, smul_zero]
  have huf : Q.polarBilin u f = 1 := by
    simp only [f, map_smul, smul_eq_mul, inv_mul_cancel₀ hquv]
  obtain ⟨g⟩ := complement_isometry hdeg u f hu hf huf
  let a : Vector (n+1) F K := (e 0,0)
  have ha : form hdeg (n+1) a = 0 := by simp only [a,form_apply,formD_e,← normForm_apply hdeg,map_zero,add_zero]
  have ha0 : a ≠ 0 := by
    intro h
    have ht := congrArg (fun x : Vector (n+1) F K => x.1 (.inl 0)) h
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

theorem singularPoints_perpendicular_connector (hdeg : Module.finrank F K = 2) (n : ℕ)
    (p r : SingularPoints (form hdeg (n+2)))
    (hpr : ¬ SingularPerp (form hdeg (n+2)) p r) :
    ∃ z, z ≠ p ∧ z ≠ r ∧ SingularPerp (form hdeg (n+2)) p z ∧
      SingularPerp (form hdeg (n+2)) r z := by
  obtain ⟨w, hw, hqw, hpw, hrw, hwp, hwr⟩ := exists_singular_perpendicular_connector hdeg n
    p.val.rep r.val.rep p.prop r.prop hpr
  let z := singularPointMk (form hdeg (n+2)) w hw hqw
  refine ⟨z, singularPointMk_ne_of_not_mem_span _ p w hw hqw hwp,
    singularPointMk_ne_of_not_mem_span _ r w hw hqw hwr, ?_, ?_⟩
  · rw [← singularPointMk_rep (form hdeg (n+2)) p]
    exact (singularPerp_mk_iff _ p.val.rep w p.val.rep_nonzero hw p.prop hqw).mpr hpw
  · rw [← singularPointMk_rep (form hdeg (n+2)) r]
    exact (singularPerp_mk_iff _ r.val.rep w r.val.rep_nonzero hw r.prop hqw).mpr hrw

/-- Distinct singular points admit a singular point nonperpendicular to both,
for the actual minus space with at least two hyperbolic pairs in every characteristic. -/
theorem singularPoints_nonperpendicular_connector (hdeg : Module.finrank F K = 2) (n : ℕ)
    (p r : SingularPoints (form hdeg (n+2))) (hpr : p ≠ r) :
    ∃ z, ¬ SingularPerp (form hdeg (n+2)) p z ∧
      ¬ SingularPerp (form hdeg (n+2)) r z := by
  obtain ⟨w, hw, hqw, hpw, hrw⟩ := exists_singular_nonperpendicular_connector_all_char
    (form hdeg (n+2)) (wittTwoFrame hdeg n) (polar_nondegenerate hdeg (n+2))
    p.val.rep r.val.rep p.val.rep_nonzero
    (singularPoints_rep_not_mem_span (form hdeg (n+2)) p r (Ne.symm hpr))
  let z := singularPointMk (form hdeg (n+2)) w hw hqw
  refine ⟨z, ?_, ?_⟩
  · rw [← singularPointMk_rep (form hdeg (n+2)) p]
    exact fun h => hpw ((singularPerp_mk_iff _ p.val.rep w p.val.rep_nonzero hw p.prop hqw).mp h)
  · rw [← singularPointMk_rep (form hdeg (n+2)) r]
    exact fun h => hrw ((singularPerp_mk_iff _ r.val.rep w r.val.rep_nonzero hw r.prop hqw).mp h)

end Atlas.Orthogonal.Minus
