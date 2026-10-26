import Mathlib.GroupTheory.Commutator.Basic

/-! UNVERIFIED source candidate. Pure group-theoretic propagation steps for
actual rank-two root identities; no root datum, coefficient field, target
order, or perfectness hypothesis occurs. -/
namespace Atlas.GroupTheory
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- Normal containment is unaffected by removing a specified conjugation. -/
theorem mem_normal_of_conjugate_mem (H : Subgroup G) [H.Normal]
    (n x : G) (h : n * x * n⁻¹ ∈ H) : x ∈ H := by
  have hc : n⁻¹ * (n * x) ∈ H := (inferInstance : H.Normal).mem_comm h
  simpa only [inv_mul_cancel_left] using hc

/-- The coefficient-one A2 endpoint: an actual conjugate commutator
certificate puts the specified element in the derived subgroup. -/
theorem mem_commutator_of_conjugate_eq_commutator (n x a b : G)
    (h : n * x * n⁻¹ = ⁅a,b⁆) : x ∈ commutator G := by
  apply mem_normal_of_conjugate_mem (commutator G) n x
  rw [h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The mixed C2 endpoint: cancel a known normal-subgroup factor from an
actual commutator, then remove the specified conjugation. -/
theorem mem_normal_of_commutator_eq_mul_conjugate
    (H : Subgroup G) [H.Normal] (a b z n x : G)
    (ha : a ∈ H) (hz : z ∈ H)
    (h : ⁅a,b⁆ = z * (n * x * n⁻¹)) : x ∈ H := by
  have hc : ⁅a,b⁆ ∈ H :=
    Subgroup.commutator_le_left H ⊤
      (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top _))
  apply mem_normal_of_conjugate_mem H n x
  exact (H.mul_mem_cancel_left hz).mp (h ▸ hc)

end Atlas.GroupTheory
