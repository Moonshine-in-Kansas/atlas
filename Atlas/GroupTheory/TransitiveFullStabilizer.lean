import Mathlib.GroupTheory.GroupAction.Quotient

namespace Atlas.GroupTheory
open MulAction

/-- A subgroup reaching the whole ambient orbit and containing the full point
stabilizer is the whole group. No finiteness or faithful action is needed. -/
theorem subgroup_eq_top_of_full_stabilizer {G X : Type*} [Group G] [MulAction G X]
    (K : Subgroup G) (x : X) (hstab : stabilizer G x ≤ K)
    (horbit : ∀ g : G, ∃ k : K, k.val • x = g • x) : K = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨k, hk⟩ := horbit g
  have hm : k.val⁻¹*g ∈ stabilizer G x := by
    change (k.val⁻¹*g) • x = x
    rw [mul_smul, ← hk, inv_smul_smul]
  have h := K.mul_mem k.property (hstab hm)
  simpa only [mul_inv_cancel_left] using h

end Atlas.GroupTheory
