import Atlas.Algebra.SplitOctonion.Basic

namespace Atlas.SplitOctonion
variable {F : Type*} [CommRing F]

theorem trace_mul_comm (a b : Carrier F) : trace (mul a b) = trace (mul b a) := by
  simp [trace, mul]; ring

/-- Associativity of the trace, not of octonion multiplication. -/
theorem trace_mul_assoc (a b c : Carrier F) :
    trace (mul (mul a b) c) = trace (mul a (mul b c)) := by
  simp [trace, mul]; ring

theorem trace_mul_cyclic (a b c : Carrier F) :
    trace (mul (mul a b) c) = trace (mul (mul b c) a) := by
  rw [trace_mul_assoc, trace_mul_comm]

end Atlas.SplitOctonion
