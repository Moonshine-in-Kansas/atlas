import Atlas.LinearAlgebra.QuadraticSingularPerpendicular
import Atlas.LinearGroups.Orthogonal.StandardComplement

/-! # Actual singular connectors for orthogonal projective geometry -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Independent directions remain independent from their difference. -/
theorem not_mem_span_difference_of_independent (u v : V) (hu : u ≠ 0)
    (hv : v ∉ Submodule.span F {u}) : u ∉ Submodule.span F {u-v} := by
  intro h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at hc
    exact hu hc.symm
  have hs : u-v = c⁻¹ • u := by
    have ht := congrArg (fun x : V => c⁻¹ • x) hc
    simpa only [smul_smul, inv_mul_cancel₀ hc0, one_smul] using ht
  apply hv
  apply Submodule.mem_span_singleton.mpr
  refine ⟨1-c⁻¹, ?_⟩
  rw [sub_smul, one_smul, ← hs]
  abel

/-- Independent directions admit a singular connector nonperpendicular to both.
The directions themselves need not be singular. -/
theorem exists_singular_nonperpendicular_connector [FiniteDimensional F V]
    (Q : QuadraticForm F V) (H : WittTwoFrame Q) (hQ : Q.polarBilin.Nondegenerate)
    (h2 : (2 : F) ≠ 0) (u v : V) (hu : u ≠ 0)
    (hv : v ∉ Submodule.span F {u}) :
    ∃ w, w ≠ 0 ∧ Q w = 0 ∧ Q.polarBilin u w ≠ 0 ∧ Q.polarBilin v w ≠ 0 := by
  obtain ⟨w, hw, hwd, huw⟩ := exists_singular_perpendicular_witness Q hQ H h2 u (u-v)
    (not_mem_span_difference_of_independent u v hu hv)
  have hp : Q.polarBilin u w = Q.polarBilin v w := by
    rw [map_sub] at hwd
    have ht := sub_eq_zero.mp hwd
    simpa only [polar_swap Q w u, polar_swap Q w v] using ht
  refine ⟨w, ?_, hw, huw, fun h => huw (hp.trans h)⟩
  intro h
  apply huw
  rw [h, map_zero]

/-- A nonzero vector perpendicular to one member of a nonorthogonal pair is not
in the line of the other member. -/
theorem perpendicular_not_mem_span (Q : QuadraticForm F V) (u v w : V)
    (hw : w ≠ 0) (huv : Q.polarBilin u v ≠ 0) (hwv : Q.polarBilin w v = 0) :
    w ∉ Submodule.span F {u} := by
  intro h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have ht := congrArg (fun x => Q.polarBilin x v) hc
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hwv] at ht
  have hc0 : c = 0 := (mul_eq_zero.mp ht).resolve_right huv
  rw [hc0, zero_smul] at hc
  exact hw hc.symm

/-- Nonorthogonal singular directions in actual B of rank at least two have a
nonzero common perpendicular singular connector, outside both original lines.
This construction also works in characteristic two. -/
theorem exists_singular_perpendicular_connectorB (n : ℕ)
    (u v : VectorB (n+2) F) (hu : formB (n+2) F u = 0)
    (hv : formB (n+2) F v = 0)
    (huv : (formB (n+2) F).polarBilin u v ≠ 0) :
    ∃ w, w ≠ 0 ∧ formB (n+2) F w = 0 ∧
      (formB (n+2) F).polarBilin u w = 0 ∧
      (formB (n+2) F).polarBilin v w = 0 ∧
      w ∉ Submodule.span F {u} ∧ w ∉ Submodule.span F {v} := by
  let Q := formB (n+2) F
  let f := (Q.polarBilin u v)⁻¹ • v
  have hqv : Q v = 0 := hv
  have hquv : Q.polarBilin u v ≠ 0 := huv
  have hf : Q f = 0 := by
    simp only [f, Q.map_smul, hqv, smul_zero]
  have huf : Q.polarBilin u f = 1 := by
    simp only [f, map_smul, smul_eq_mul, inv_mul_cancel₀ hquv]
  obtain ⟨g⟩ := complement_isometryB u f hu hf huf
  let a : VectorB (n+1) F := (e 0, 0)
  have ha : formB (n+1) F a = 0 := by
    simp only [a, formB_apply, formD_e, zero_pow (by decide : 2 ≠ 0), add_zero]
  have ha0 : a ≠ 0 := by
    intro h
    have ht := congrArg (fun x : VectorB (n+1) F => x.1 (.inl 0)) h
    have hone : (1 : F) = 0 := by simpa [a, e] using ht
    exact one_ne_zero hone
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
end Atlas.Orthogonal
