import Atlas.LinearGroups.Orthogonal.SingularLineKernel

/-! # Scalar singular-line kernel from a hyperbolic triangle -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem singular_line_kernel_scalar_of_triangle (Q : QuadraticForm F V)
    (e f s : V) (he : Q e = 0) (hf : Q f = 0) (hs : Q s = 0)
    (hef : Q.polarBilin e f = 1) (hes : Q.polarBilin e s ≠ 0) (hfs : Q.polarBilin f s ≠ 0)
    (z : isometrySubgroup Q) (hz : ∀ x, Q x = 0 → ∃ c : F, z.val x = c • x) :
    ∃ c : F, c^2 = 1 ∧ ∀ x : V, z.val x = c • x := by
  obtain ⟨c,hc⟩ := hz e he
  obtain ⟨d,hd⟩ := hz f hf
  obtain ⟨k,hk⟩ := hz s hs
  have hck : c*k = 1 := by
    have h := isometry_polar Q (isometryCarrierEquiv Q z) e s
    change Q.polarBilin (z.val e) (z.val s) = Q.polarBilin e s at h
    rw [hc,hk] at h
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul] at h
    apply mul_right_cancel₀ hes
    simpa only [mul_assoc,mul_left_comm,mul_comm,one_mul] using h
  have hdk : d*k = 1 := by
    have h := isometry_polar Q (isometryCarrierEquiv Q z) f s
    change Q.polarBilin (z.val f) (z.val s) = Q.polarBilin f s at h
    rw [hd,hk] at h
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul] at h
    apply mul_right_cancel₀ hfs
    simpa only [mul_assoc,mul_left_comm,mul_comm,one_mul] using h
  have hk0 : k ≠ 0 := by intro h; rw [h,mul_zero] at hck; exact zero_ne_one hck
  have hdc : d = c := mul_right_cancel₀ hk0 (hdk.trans hck.symm)
  rw [hdc] at hd
  have hcc : c*c = 1 := by
    have h := isometry_polar Q (isometryCarrierEquiv Q z) e f
    change Q.polarBilin (z.val e) (z.val f) = Q.polarBilin e f at h
    simpa only [hc, hd, map_smul, LinearMap.smul_apply, smul_eq_mul,
      hef, mul_one] using h
  have hw (w : complement Q e f) : z.val w.val = c • w.val := by
    let s := w.val + e - Q w.val • f
    have hs : Q s = 0 := complement_singular_decomposition Q e f
      he hf hef w
    obtain ⟨t, ht⟩ := hz s hs
    have hsf : Q.polarBilin s f = 1 := by
      have hwf : Q.polarBilin w.val f = 0 := w.prop.2
      have hff : Q.polarBilin f f = 0 := by rw [polar_self, hf, mul_zero]
      simp only [s, map_sub, map_add, map_smul, LinearMap.sub_apply,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hwf, hef,
        hff, mul_zero, zero_add, sub_zero]
    have htc : t*c = 1 := by
      have h := isometry_polar Q (isometryCarrierEquiv Q z) s f
      change Q.polarBilin (z.val s) (z.val f) = Q.polarBilin s f at h
      simpa only [ht, hd, map_smul, LinearMap.smul_apply, smul_eq_mul, hsf, mul_one, mul_comm] using h
    have htc' : t = c := by
      calc
        t = t * (c*c) := by rw [hcc, mul_one]
        _ = (t*c)*c := (mul_assoc _ _ _).symm
        _ = c := by rw [htc, one_mul]
    rw [htc'] at ht
    change z.val (w.val + e - Q w.val • f) =
      c • (w.val + e - Q w.val • f) at ht
    rw [map_sub, map_add, map_smul, hc, hd, smul_sub, smul_add,
      smul_comm c (Q w.val) f] at ht
    exact add_right_cancel (sub_left_inj.mp ht)
  refine ⟨c, by simpa only [pow_two] using hcc, ?_⟩
  intro x
  let t := split Q e f he hf hef
  have hx := t.symm_apply_apply x
  change (t x).1.1 • e + (t x).1.2 • f + (t x).2.val = x at hx
  rw [← hx, map_add, map_add, map_smul, map_smul, hc, hd, hw,
    smul_add, smul_add, smul_comm c (t x).1.1 e, smul_comm c (t x).1.2 f]

end Atlas.Orthogonal
