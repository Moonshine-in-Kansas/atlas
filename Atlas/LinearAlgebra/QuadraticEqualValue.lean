import Atlas.LinearAlgebra.QuadraticReflection

/-! # Reflection transport of equal nonzero quadratic values -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

theorem sub_value (u v : V) : Q (u-v) = Q u + Q v - Q.polarBilin u v := by
  rw [sub_eq_add_neg, ← neg_one_smul F v, add_smul]
  ring

theorem reflection_equal_value (u v : V) (hval : Q u = Q v) (huv : Q (u-v) ≠ 0) :
    reflectionLinear Q (u-v) huv u = v := by
  have hp : Q.polarBilin u (u-v) = Q (u-v) := by
    rw [map_sub, polar_self, sub_value, hval]
    ring
  rw [reflectionLinear_apply, hp, inv_mul_cancel₀ huv, one_smul, sub_sub_cancel]

@[simp] theorem reflection_self (a : V) (ha : Q a ≠ 0) : reflectionLinear Q a ha a = -a :=
  Module.reflection_apply_self _

/-- One or two actual reflections transport vectors of equal nonzero norm in odd characteristic. -/
theorem equal_value_transport (h2 : (2 : F) ≠ 0) (u v : V)
    (hu : Q u ≠ 0) (hval : Q u = Q v) :
    ∃ g : Q.IsometryEquiv Q, g u = v := by
  by_cases hsub : Q (u-v) = 0
  · have hsum : Q (u+v) ≠ 0 := by
      have hs := sub_value Q u v
      have ha := QuadraticMap.map_add Q u v
      change Q (u+v) = Q u + Q v + Q.polarBilin u v at ha
      have he : Q (u+v) = (2 : F)^2 * Q u := by rw [hval] at hs ha ⊢; linear_combination ha + hs - hsub
      rw [he]
      exact mul_ne_zero (pow_ne_zero _ h2) hu
    have hd : Q (u-(-v)) ≠ 0 := by simpa only [sub_neg_eq_add] using hsum
    let r := reflectionIsometry Q (u-(-v)) hd
    let s := reflectionIsometry Q v (hval ▸ hu)
    refine ⟨r.trans s, ?_⟩
    change s (r u) = v
    have hr : r u = -v := reflection_equal_value Q u (-v) (by rwa [Q.map_neg]) hd
    rw [hr, map_neg]
    change -(reflectionLinear Q v (hval ▸ hu) v) = v
    rw [reflection_self, neg_neg]
  · exact ⟨reflectionIsometry Q (u-v) hsub, reflection_equal_value Q u v hval hsub⟩

end Atlas.Quadratic
