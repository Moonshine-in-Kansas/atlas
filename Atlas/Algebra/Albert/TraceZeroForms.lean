import Atlas.Algebra.Albert.TraceZero
import Atlas.Algebra.Albert.CrossProduct

/-! Characteristic-two forms and projected cross product on the actual trace
kernel. Identities hold over arbitrary coefficient rings of characteristic two,
so they also apply with independent polynomial variables. -/
namespace Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def traceZeroQuadratic (w : TraceZero F) : F := quadraticTrace w

def traceZeroCubic (w : TraceZero F) : F := norm w

theorem traceZeroCubicDecomposition (t : F) (w : TraceZero F) :
    norm (t • unit + (w : Carrier F)) =
      t^3 + t * traceZeroQuadratic w + traceZeroCubic w := by
  rw [add_comm, norm_add_smul, adjoint_unit, tracePairing_unit, trace_adjoint,
    tracePairing_unit, trace_traceZero, norm_unit]
  simp only [traceZeroQuadratic, traceZeroCubic]
  ring

theorem traceZeroQuadratic_constantTerm (w : TraceZero F) :
    traceZeroQuadratic w = norm (unit + (w : Carrier F)) + norm w + 1 := by
  have h := traceZeroCubicDecomposition (1 : F) w
  simp only [one_smul, one_pow, one_mul, traceZeroCubic] at h
  rw [h]
  linear_combination -(norm (w : Carrier F) + 1) * (CharTwo.two_eq_zero (R:=F))

def traceZeroPolar (u v : TraceZero F) : F := tracePairing u v

theorem traceZeroPolar_quadratic (u v : TraceZero F) :
    traceZeroPolar u v = traceZeroQuadratic (u+v) - traceZeroQuadratic u - traceZeroQuadratic v := by
  simp [traceZeroPolar, tracePairing, traceZeroQuadratic, CharTwo.neg_eq]

theorem traceZeroPolar_comm (u v : TraceZero F) :
    traceZeroPolar u v = traceZeroPolar v u := tracePairing_comm _ _

theorem traceZeroPolar_add_left (u v w : TraceZero F) :
    traceZeroPolar (u+v) w = traceZeroPolar u w + traceZeroPolar v w :=
  tracePairing_add_left _ _ _

theorem traceZeroPolar_smul_left (a : F) (u v : TraceZero F) :
    traceZeroPolar (a • u) v = a * traceZeroPolar u v :=
  tracePairing_smul_left _ _ _

theorem traceZeroPolar_self (u : TraceZero F) : traceZeroPolar u u = 0 := by
  have h : tracePairing (u : Carrier F) u = trace (u : Carrier F)^2 - 2 * quadraticTrace u := by
    simp [tracePairing, trace, quadraticTrace, SplitOctonion.norm]
    ring
  change tracePairing (u : Carrier F) u = 0
  rw [h, trace_traceZero, (CharTwo.two_eq_zero (R:=F))]
  ring

theorem traceZeroPolar_nondegenerate (u : TraceZero F)
    (h : ∀ v, traceZeroPolar u v = 0) : u = 0 := by
  apply Subtype.ext
  apply tracePairing_nondegenerate
  intro y
  rw [← traceZero_decomposition y, tracePairing_comm, tracePairing_add_left,
    tracePairing_smul_left, tracePairing_comm unit, tracePairing_unit,
    trace_traceZero, mul_zero, zero_add, tracePairing_comm]
  exact h (traceZeroProjection y)

def traceZeroCross (u v : TraceZero F) : TraceZero F := traceZeroProjection (cross u v)

theorem traceZeroCross_formula (u v : TraceZero F) :
    (traceZeroCross u v : Carrier F) = cross u v + traceZeroPolar u v • unit := by
  rw [traceZeroCross, traceZeroProjection_formula, trace_cross]
  simp [traceZeroPolar, CharTwo.neg_eq]

theorem traceZeroCross_comm (u v : TraceZero F) : traceZeroCross u v = traceZeroCross v u := by
  simp only [traceZeroCross, cross_comm]

theorem traceZeroCross_add_left (u v w : TraceZero F) :
    traceZeroCross (u+v) w = traceZeroCross u w + traceZeroCross v w := by
  simp only [traceZeroCross, Submodule.coe_add, cross_add_left, map_add]

theorem traceZeroCross_smul_left (a : F) (u v : TraceZero F) :
    traceZeroCross (a • u) v = a • traceZeroCross u v := by
  simp only [traceZeroCross, Submodule.coe_smul, cross_smul_left, map_smul]

theorem traceZeroCross_self (u : TraceZero F) : traceZeroCross u u = 0 := by
  have hz : (u : Carrier F) + (u : Carrier F) = 0 := by
    rw [← two_smul F, (CharTwo.two_eq_zero (R:=F)), zero_smul]
  have ha : adjoint (0 : Carrier F) = 0 := by
    apply Prod.ext
    · funext i; fin_cases i <;> simp [adjoint, SplitOctonion.norm]
    · funext i j; fin_cases i <;> fin_cases j <;>
        simp [adjoint, SplitOctonion.norm, SplitOctonion.conjugate,
          SplitOctonion.mul, SplitOctonion.trace, SplitOctonion.unit]
  have hc : cross (u : Carrier F) u = 0 := by
    rw [cross, hz, ha, zero_sub, sub_eq_add_neg, ← neg_add, ← two_smul F,
      (CharTwo.two_eq_zero (R:=F)), zero_smul, neg_zero]
  simp only [traceZeroCross, hc, map_zero]

theorem traceZeroPolar_cross (u v w : TraceZero F) :
    traceZeroPolar (traceZeroCross u v) w = tracePairing (cross u v) w := by
  unfold traceZeroPolar
  rw [traceZeroCross_formula, tracePairing_add_left, tracePairing_smul_left,
    tracePairing_comm unit, tracePairing_unit, trace_traceZero, mul_zero, add_zero]

theorem traceZeroPolar_cross_cyclic (u v w : TraceZero F) :
    traceZeroPolar (traceZeroCross u v) w = traceZeroPolar u (traceZeroCross v w) := by
  rw [traceZeroPolar_comm u, traceZeroPolar_cross, traceZeroPolar_cross,
    tracePairing_cross, tracePairing_comm]

end Atlas.Albert

