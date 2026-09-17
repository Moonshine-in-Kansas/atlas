import Atlas.LinearGroups.Orthogonal.Basic
import Atlas.LinearAlgebra.QuadraticWittTwo
import Atlas.LinearAlgebra.QuadraticSingularSpan

/-! # Scalar kernel of the action on singular one-dimensional subspaces -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- Perpendicular singular directions linked by their singular sum have the same scalar. -/
theorem singular_line_scalars_equal (z : isometrySubgroup Q)
    (hz : ∀ x, Q x = 0 → ∃ c : F, z.val x = c • x)
    (e f a b : V) (he : Q e = 0) (ha : Q a = 0)
    (hea : Q.polarBilin e a = 0) (hef : Q.polarBilin e f = 1)
    (hab : Q.polarBilin a b = 1) (haf : Q.polarBilin a f = 0)
    (heb : Q.polarBilin e b = 0)
    (c d : F) (hc : z.val e = c • e) (hd : z.val a = d • a) : c = d := by
  have hsum : Q (e+a) = 0 := by
    rw [QuadraticMap.map_add Q]
    change Q e + Q a + Q.polarBilin e a = 0
    rw [he, ha, hea, add_zero, add_zero]
  obtain ⟨k, hk⟩ := hz (e+a) hsum
  rw [map_add, hc, hd] at hk
  have hck := congrArg (fun x => Q.polarBilin x f) hk
  have hdk := congrArg (fun x => Q.polarBilin x b) hk
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hef, haf, mul_one, mul_zero, add_zero] at hck
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, heb, hab, mul_one, mul_zero, zero_add] at hdk
  exact hck.trans hdk.symm

/-- A full isometry preserving each singular line is scalar, given two hyperbolic planes.
This argument works in every characteristic and does not assume finite dimension. -/
theorem singular_line_kernel_scalar (H : WittTwoFrame Q) (z : isometrySubgroup Q)
    (hz : ∀ x, Q x = 0 → ∃ c : F, z.val x = c • x) :
    ∃ c : F, c^2 = 1 ∧ ∀ x : V, z.val x = c • x := by
  obtain ⟨c, hc⟩ := hz H.e₁ H.qe₁
  obtain ⟨d, hd⟩ := hz H.f₁ H.qf₁
  obtain ⟨k, hk⟩ := hz H.e₂ H.qe₂
  have hck : c = k := singular_line_scalars_equal Q z hz H.e₁ H.f₁ H.e₂ H.f₂
    H.qe₁ H.qe₂ ((polar_swap Q _ _).trans H.ee) H.pair₁ H.pair₂ H.ef
    ((polar_swap Q _ _).trans H.fe) c k hc hk
  have hdk : d = k := singular_line_scalars_equal Q z hz H.f₁ H.e₁ H.e₂ H.f₂
    H.qf₁ H.qe₂ ((polar_swap Q _ _).trans H.ef)
    ((polar_swap Q _ _).trans H.pair₁) H.pair₂ H.ee
    ((polar_swap Q _ _).trans H.ff) d k hd hk
  have hdc : d = c := hdk.trans hck.symm
  rw [hdc] at hd
  have hcc : c*c = 1 := by
    have h := isometry_polar Q (isometryCarrierEquiv Q z) H.e₁ H.f₁
    change Q.polarBilin (z.val H.e₁) (z.val H.f₁) = Q.polarBilin H.e₁ H.f₁ at h
    simpa only [hc, hd, map_smul, LinearMap.smul_apply, smul_eq_mul,
      H.pair₁, mul_one] using h
  have hw (w : complement Q H.e₁ H.f₁) : z.val w.val = c • w.val := by
    let s := w.val + H.e₁ - Q w.val • H.f₁
    have hs : Q s = 0 := complement_singular_decomposition Q H.e₁ H.f₁
      H.qe₁ H.qf₁ H.pair₁ w
    obtain ⟨t, ht⟩ := hz s hs
    have hsf : Q.polarBilin s H.f₁ = 1 := by
      have hwf : Q.polarBilin w.val H.f₁ = 0 := w.prop.2
      have hff : Q.polarBilin H.f₁ H.f₁ = 0 := by rw [polar_self, H.qf₁, mul_zero]
      simp only [s, map_sub, map_add, map_smul, LinearMap.sub_apply,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hwf, H.pair₁,
        hff, mul_zero, zero_add, sub_zero]
    have htc : t*c = 1 := by
      have h := isometry_polar Q (isometryCarrierEquiv Q z) s H.f₁
      change Q.polarBilin (z.val s) (z.val H.f₁) = Q.polarBilin s H.f₁ at h
      simpa only [ht, hd, map_smul, LinearMap.smul_apply, smul_eq_mul, hsf, mul_one, mul_comm] using h
    have htc' : t = c := by
      calc
        t = t * (c*c) := by rw [hcc, mul_one]
        _ = (t*c)*c := (mul_assoc _ _ _).symm
        _ = c := by rw [htc, one_mul]
    rw [htc'] at ht
    change z.val (w.val + H.e₁ - Q w.val • H.f₁) =
      c • (w.val + H.e₁ - Q w.val • H.f₁) at ht
    rw [map_sub, map_add, map_smul, hc, hd, smul_sub, smul_add,
      smul_comm c (Q w.val) H.f₁] at ht
    exact add_right_cancel (sub_left_inj.mp ht)
  refine ⟨c, by simpa only [pow_two] using hcc, ?_⟩
  intro x
  let t := split Q H.e₁ H.f₁ H.qe₁ H.qf₁ H.pair₁
  have hx := t.symm_apply_apply x
  change (t x).1.1 • H.e₁ + (t x).1.2 • H.f₁ + (t x).2.val = x at hx
  rw [← hx, map_add, map_add, map_smul, map_smul, hc, hd, hw,
    smul_add, smul_add, smul_comm c (t x).1.1 H.e₁, smul_comm c (t x).1.2 H.f₁]
/-- Nonzero-direction formulation for the actual projective singular-point action. -/
theorem singular_projective_kernel_scalar (H : WittTwoFrame Q) (z : isometrySubgroup Q)
    (hz : ∀ x, x ≠ 0 → Q x = 0 → ∃ c : F, z.val x = c • x) :
    ∃ c : F, c^2 = 1 ∧ ∀ x : V, z.val x = c • x := by
  apply singular_line_kernel_scalar Q H z
  intro x hx
  by_cases hzero : x = 0
  · subst x
    exact ⟨0, by simp only [map_zero, smul_zero]⟩
  · exact hz x hzero hx
end Atlas.Orthogonal

