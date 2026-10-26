import Atlas.Sporadic.Janko1.GeneratorActions
import Mathlib.GroupTheory.OrderOfElement

/-! Local relations in the actual octonion automorphism group. -/
namespace Atlas.Janko1

private theorem automorphism_ext_basis (g h : G2.Model Field)
    (he : ∀ i : Fin 8, g.val (SplitOctonion.basisVector i) =
      h.val (SplitOctonion.basisVector i)) : g = h := by
  apply linearRepresentation_injective
  exact SplitOctonion.linearMap_ext _ _ he

set_option maxRecDepth 8192 in
private theorem generators_ne_one : ∀ g : Fin 4, generator g ≠ 1 := by
  intro g h
  have he := congrArg (fun a : G2.Model Field => a.val (imaginaryVector (if g = 1 then 1 else 0))) h
  have hn : ∀ g : Fin 4, (generator g).val (imaginaryVector (if g = 1 then 1 else 0)) ≠ imaginaryVector (if g = 1 then 1 else 0) := by
    decide
  exact hn g he

theorem orderOf_P : orderOf P = 7 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime P_pow (generators_ne_one 0)
theorem orderOf_Q : orderOf Q = 3 := orderOf_eq_prime Q_pow (generators_ne_one 1)
theorem orderOf_R : orderOf R = 2 := orderOf_eq_prime R_pow (generators_ne_one 2)
theorem orderOf_S : orderOf S = 2 := orderOf_eq_prime S_pow (generators_ne_one 3)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem Q_mul_P : Q * P = P^2 * Q := by
  apply automorphism_ext_basis
  decide

theorem Q_conjugates_P : Q * P * Q⁻¹ = P^2 := by
  rw [Q_mul_P, mul_assoc, mul_inv_cancel, mul_one]

end Atlas.Janko1
