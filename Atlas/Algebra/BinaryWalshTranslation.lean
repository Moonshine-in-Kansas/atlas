import Atlas.Algebra.BinaryWalshSquare

namespace Atlas.Algebra

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- Translating a character by the actual polar functional determines the exact
Walsh sign. This identity retains the phase, not merely its absolute value. -/
theorem binaryWalsh_translate_polar (q : QuadraticMap (ZMod 2) V (ZMod 2))
    (a : V →+ ZMod 2) (t : V) :
    binaryWalsh q (a + (q.polarBilin t).toAddMonoidHom) =
      binaryWalshSign (q t + a t) * binaryWalsh q a := by
  classical
  have hp (x : V) :
      binaryWalshSign (q x + (a + (q.polarBilin t).toAddMonoidHom) x) =
        binaryWalshSign (q t + a t) * binaryWalshSign (q (x + t) + a (x + t)) := by
    rw [← binaryWalshSign_add]
    congr 1
    change q x + (a x + q.polarBilin t x) = _
    rw [binaryWalsh_quadratic_add, map_add]
    have hb : q.polarBilin x t = q.polarBilin t x := QuadraticMap.polar_comm q x t
    rw [hb]
    calc
      _ = (q x + a x + q.polarBilin t x) + ((q t + a t) + (q t + a t)) := by
        rw [CharTwo.add_self_eq_zero, add_zero, add_assoc]
      _ = _ := by ac_rfl
  simp only [binaryWalsh, hp, ← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.addRight t) _ _ (fun _ => rfl)

omit [Fintype V] in
/-- The phase function for translated Walsh signs has precisely the original
polar form. Together with `binaryWalsh_translate_polar`, this records the dual
quadratic signs without an arbitrary choice of an overall sign. -/
theorem binaryWalsh_phase_polar (q : QuadraticMap (ZMod 2) V (ZMod 2))
    (a : V →+ ZMod 2) (s t : V) :
    (q (s + t) + a (s + t)) + (q s + a s) + (q t + a t) = q.polarBilin s t := by
  rw [binaryWalsh_quadratic_add, map_add]
  calc
    _ = q.polarBilin s t + ((q s + a s) + (q s + a s)) +
      ((q t + a t) + (q t + a t)) := by ac_rfl
    _ = _ := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero, add_zero]

end Atlas.Algebra
