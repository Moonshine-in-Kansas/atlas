import Atlas.LinearGroups.Orthogonal.Elementary
import Atlas.LinearAlgebra.QuadraticSiegelTransport
import Atlas.LinearAlgebra.QuadraticSingularPerpendicular

/-! # Elementary transitivity on nonsingular vectors of a fixed quadratic value -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- One actual elementary transformation gives equal-value transport along a singular direction. -/
theorem elementary_transport_with_direction (u v w : V) (hw : Q w = 0)
    (hval : Q u = Q v) (hp : Q.polarBilin u w = Q.polarBilin v w)
    (hne : Q.polarBilin u w ≠ 0) :
    ∃ g : isometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val u = v := by
  let t := transportParameter Q u v w
  have ht := transportParameter_perp Q u v w hp
  exact ⟨siegelElement Q w t hw ht, siegelElement_mem Q w t hw ht,
    siegel_equal_value_transport Q u v w hval hne⟩

/-- Equal nonzero quadratic values can be collinear with their difference only at opposites. -/
theorem nonsingular_not_span_difference (u v : V) (hu : Q u ≠ 0)
    (hval : Q u = Q v) (hopp : v ≠ -u) : u ∉ Submodule.span F {u-v} := by
  rintro h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have hcu : u = c • (u-v) := hc.symm
  have hd : Q (u-v) ≠ 0 := by
    intro hd
    apply hu
    rw [hcu, Q.map_smul, hd, smul_zero]
  have hp := congrArg (fun x : V => Q.polarBilin x (u-v)) hc
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, polar_self,
    difference_polar_value Q u v hval] at hp
  have hc2 : (2 : F) * c = 1 := by
    apply (mul_right_cancel₀ hd)
    linear_combination hp
  have he : u+u = u-v := by
    have ht := congrArg (fun z : V => (2 : F) • z) hcu
    rw [smul_smul, hc2, one_smul] at ht
    simpa only [two_smul] using ht
  apply hopp
  apply eq_neg_iff_add_eq_zero.mpr
  have ht := congrArg (fun z : V => z+v-u) he
  convert ht using 1 <;> abel

variable [FiniteDimensional F V] (H : WittTwoFrame Q)
  (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

include H hQ h2 in
/-- Apart from opposite vectors, one Siegel transformation suffices in Witt index at least two. -/
theorem elementary_transport_not_opposite (u v : V) (hu : Q u ≠ 0)
    (hval : Q u = Q v) (hopp : v ≠ -u) :
    ∃ g : isometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val u = v := by
  obtain ⟨w, hw, hwd, huw⟩ := exists_singular_perpendicular_witness Q hQ H h2 u (u-v)
    (nonsingular_not_span_difference Q u v hu hval hopp)
  have hp : Q.polarBilin u w = Q.polarBilin v w := by
    rw [map_sub] at hwd
    have hp := sub_eq_zero.mp hwd
    simpa only [polar_swap Q w u, polar_swap Q w v] using hp
  exact elementary_transport_with_direction Q u v w hw hval hp huw

include H hQ h2 in
/-- The actual elementary group is transitive on each nonzero quadratic-value shell. -/
theorem elementary_transport_equal_value (u v : V) (hu : Q u ≠ 0)
    (hval : Q u = Q v) :
    ∃ g : isometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val u = v := by
  by_cases hopp : v = -u
  · subst v
    obtain ⟨a, b, ha, hb, hab, hau, hbu⟩ := hyperbolic_pair_in_perpendicular Q H hQ h2 u
    have hane : a ≠ 0 := by
      intro h
      rw [h, map_zero, LinearMap.zero_apply] at hab
      exact zero_ne_one hab
    have hua : Q.polarBilin u a = 0 := (polar_swap Q u a).trans hau
    have hza : Q (u+a) = Q u := by
      rw [QuadraticMap.map_add Q]
      change Q u + Q a + Q.polarBilin u a = Q u
      rw [ha, hua, add_zero, add_zero]
    have hzn : u+a ≠ -u := by
      intro h
      have he : a = (-2 : F) • u := by
        have ht := congrArg (fun z : V => z-u) h
        convert ht using 1 <;> module
      rw [he, Q.map_smul, smul_eq_mul] at ha
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) (neg_ne_zero.mpr h2)) hu ha
    have hzn' : -u ≠ -(u+a) := by
      intro h
      have ht := neg_injective h.symm
      apply hane
      exact add_left_cancel (ht.trans (add_zero u).symm)
    obtain ⟨g, hg, hgu⟩ := elementary_transport_not_opposite Q H hQ h2 u (u+a) hu hza.symm hzn
    obtain ⟨k, hk, hka⟩ := elementary_transport_not_opposite Q H hQ h2 (u+a) (-u)
      (hza ▸ hu) (hza.trans (Q.map_neg u).symm) hzn'
    refine ⟨k*g, (elementarySubgroup Q).mul_mem hk hg, ?_⟩
    change k.val (g.val u) = -u
    rw [hgu, hka]
  · exact elementary_transport_not_opposite Q H hQ h2 u v hu hval hopp

end Atlas.Orthogonal

