import Mathlib.Algebra.Ring.Basic
import Atlas.GroupTheory.NormalCommutatorPropagation

/-! Source candidate: normal-subgroup propagation in either direction across
an explicitly supplied mixed root-word relation. No group identification,
finite-field assumption or division by two occurs. -/

namespace Atlas.GroupTheory
open scoped commutatorElement

variable {R G : Type*} [Ring R] [Group G]

/-- Short-root containment implies long-root containment via the mixed word
with short parameter one. The relation itself is an explicit premise. -/
theorem long_family_mem_normal_of_short_of_mixed_relation
    (H : Subgroup G) [H.Normal] (x y : R → G) (u v : G)
    (hrelation : ∀ s t : R, ⁅x s, y t⁆ =
      (v * x (-s * t) * v⁻¹) * (u * y (s ^ 2 * t) * u⁻¹))
    (hx : ∀ t : R, x t ∈ H) (t : R) : y t ∈ H := by
  have h : ⁅x 1, y t⁆ =
      (v * x (-t) * v⁻¹) * (u * y t * u⁻¹) := by
    simpa only [neg_one_mul, one_pow, one_mul] using hrelation 1 t
  exact mem_normal_of_commutator_eq_mul_conjugate H (x 1) (y t)
    (v * x (-t) * v⁻¹) u (y t) (hx 1)
    ((inferInstance : H.Normal).conj_mem _ (hx (-t)) v) h

/-- Long-root containment implies short-root containment via the same mixed
word with long parameter one. This direction needs no coefficient inversion. -/
theorem short_family_mem_normal_of_long_of_mixed_relation
    (H : Subgroup G) [H.Normal] (x y : R → G) (u v : G)
    (hrelation : ∀ s t : R, ⁅x s, y t⁆ =
      (v * x (-s * t) * v⁻¹) * (u * y (s ^ 2 * t) * u⁻¹))
    (hy : ∀ t : R, y t ∈ H) (t : R) : x t ∈ H := by
  have h : ⁅x (-t), y 1⁆ =
      (v * x t * v⁻¹) * (u * y ((-t) ^ 2) * u⁻¹) := by
    simpa only [neg_neg, mul_one] using hrelation (-t) 1
  have hc : ⁅x (-t), y 1⁆ ∈ H :=
    Subgroup.commutator_le_right ⊤ H
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (hy 1))
  have hw : u * y ((-t) ^ 2) * u⁻¹ ∈ H :=
    (inferInstance : H.Normal).conj_mem _ (hy ((-t) ^ 2)) u
  apply mem_normal_of_conjugate_mem H v (x t)
  exact (H.mul_mem_cancel_right hw).mp (h ▸ hc)

/-- An actual coefficient-one mixed relation makes the two complete root
families have the same normal containment. -/
theorem root_family_mem_normal_iff_of_mixed_relation
    (H : Subgroup G) [H.Normal] (x y : R → G) (u v : G)
    (hrelation : ∀ s t : R, ⁅x s, y t⁆ =
      (v * x (-s * t) * v⁻¹) * (u * y (s ^ 2 * t) * u⁻¹)) :
    (∀ t : R, x t ∈ H) ↔ (∀ t : R, y t ∈ H) := by
  exact ⟨fun hx t => long_family_mem_normal_of_short_of_mixed_relation
    H x y u v hrelation hx t,
    fun hy t => short_family_mem_normal_of_long_of_mixed_relation
      H x y u v hrelation hy t⟩

end Atlas.GroupTheory
