import Atlas.Algebra.Albert.TraceZeroForms

/-! The domain of the intended partial twisted product. It is bilinear
isotropy and zero projected cross, not quadratic isotropy of each vector.
No star values or group stabilizer are asserted by this module. -/
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def StarDomain (u v : TraceZero F) : Prop :=
  traceZeroPolar u v = 0 ∧ traceZeroCross u v = 0

theorem starDomain_comm (u v : TraceZero F) : StarDomain u v ↔ StarDomain v u := by
  simp only [StarDomain, traceZeroPolar_comm u v, traceZeroCross_comm u v]

theorem starDomain_self (u : TraceZero F) : StarDomain u u :=
  ⟨traceZeroPolar_self u, traceZeroCross_self u⟩

theorem starDomain_smul_left (a : F) {u v : TraceZero F} (h : StarDomain u v) :
    StarDomain (a • u) v := by
  constructor
  · rw [traceZeroPolar_smul_left, h.1, mul_zero]
  · rw [traceZeroCross_smul_left, h.2, smul_zero]

theorem starDomain_smul_right (a : F) {u v : TraceZero F} (h : StarDomain u v) :
    StarDomain u (a • v) :=
  (starDomain_comm _ _).mpr (starDomain_smul_left a ((starDomain_comm _ _).mp h))

theorem starDomain_add_left {u v w : TraceZero F} (hu : StarDomain u w)
    (hv : StarDomain v w) : StarDomain (u+v) w := by
  constructor
  · rw [traceZeroPolar_add_left, hu.1, hv.1, add_zero]
  · rw [traceZeroCross_add_left, hu.2, hv.2, add_zero]

end Atlas.ReeF4
