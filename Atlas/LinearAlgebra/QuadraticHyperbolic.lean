import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Tactic.Ring

/-! # Hyperbolic partners for quadratic forms without division by two -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- The convention is the unhalved polar form, in every characteristic. -/
theorem add_smul (x y : V) (a : F) :
    Q (x + a • y) = Q x + a ^ 2 * Q y + a * Q.polarBilin x y := by
  rw [QuadraticMap.map_add Q, Q.map_smul]
  change Q x + (a * a) * Q y + Q.polarBilin x (a • y) = _
  rw [map_smul]
  simp only [smul_eq_mul, pow_two]

theorem polar_swap (x y : V) : Q.polarBilin x y = Q.polarBilin y x :=
  QuadraticMap.polar_comm Q x y

theorem polar_self (x : V) : Q.polarBilin x x = 2 * Q x := by
  change QuadraticMap.polar Q x x = _
  rw [QuadraticMap.polar_self]
  simp [two_smul, two_mul]

/-- Completing a normalized partner to a singular one uses no factor of 1/2. -/
theorem partner_correction (u f : V) (hu : Q u = 0)
    (huf : Q.polarBilin u f = 1) :
    Q (f - Q f • u) = 0 ∧ Q.polarBilin u (f - Q f • u) = 1 := by
  have hfu : Q.polarBilin f u = 1 := (polar_swap Q f u).trans huf
  have huu : Q.polarBilin u u = 0 := by rw [polar_self, hu, mul_zero]
  constructor
  · rw [sub_eq_add_neg, ← neg_smul, add_smul, hu, hfu]
    ring
  · rw [map_sub, map_smul, huu, smul_zero, sub_zero, huf]

/-- Any vector outside the polar radical has a partner of pairing one. -/
theorem exists_normalized_partner (u : V)
    (hu : ¬ ∀ w, Q.polarBilin u w = 0) : ∃ f, Q.polarBilin u f = 1 := by
  classical
  obtain ⟨w,hw⟩ := not_forall.mp hu
  refine ⟨(Q.polarBilin u w)⁻¹ • w, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]

/-- Every singular vector outside the polar radical begins a hyperbolic pair. -/
theorem exists_hyperbolic_partner (u : V) (hq : Q u = 0)
    (hu : ¬ ∀ w, Q.polarBilin u w = 0) :
    ∃ f, Q f = 0 ∧ Q.polarBilin u f = 1 := by
  obtain ⟨f,hf⟩ := exists_normalized_partner Q u hu
  exact ⟨f - Q f • u, partner_correction Q u f hq hf⟩

/-- Explicit parametrization of singular partners by a perpendicular complement. -/
theorem partner_from_perpendicular (u f w : V) (hu : Q u = 0) (hf : Q f = 0)
    (huf : Q.polarBilin u f = 1) (huw : Q.polarBilin u w = 0)
    (hfw : Q.polarBilin f w = 0) :
    Q (f + w - Q w • u) = 0 ∧ Q.polarBilin u (f + w - Q w • u) = 1 := by
  have hq : Q (f+w) = Q w := by
    rw [QuadraticMap.map_add Q]
    change Q f + Q w + Q.polarBilin f w = Q w
    rw [hf, hfw, zero_add, add_zero]
  have hp : Q.polarBilin u (f+w) = 1 := by rw [map_add,huf,huw,add_zero]
  simpa only [hq] using partner_correction Q u (f+w) hu hp

end Atlas.Quadratic
