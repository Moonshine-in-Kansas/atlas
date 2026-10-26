import Atlas.Algebra.Albert.ShortRootMaps
import Atlas.Algebra.Albert.RankOneConsequences

/-! The self-pairing displacement of an actual short-root transformation.
This is an integral polynomial identity, including characteristics two and three. -/
namespace Atlas.Albert
variable {F : Type*} [CommRing F]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
theorem tracePairing_shortRootLinear (i : Fin 8) (t : F) (y : Carrier F) :
    tracePairing y (shortRootLinear i t y) =
      tracePairing y y - t ^ 2 * (y.2 2 (7-i)) ^ 2 := by
  rw [tracePairing_coordinates, tracePairing_coordinates]
  fin_cases i <;>
    simp [shortRootLinear, shortRootFormula, SplitOctonion.basisVector,
      SplitOctonion.trace, SplitOctonion.mul, SplitOctonion.conjugate,
      SplitOctonion.unit, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem tracePairing_self (y : Carrier F) :
    tracePairing y y = trace y ^ 2 - 2 * quadraticTrace y := by
  simp [tracePairing, trace, quadraticTrace, SplitOctonion.norm]
  ring

variable {K : Type*} [Field K]

theorem tracePairing_shortRootLinear_white (i : Fin 8) (t : K) (y : Carrier K)
    (ha : adjoint y=0) (ht : trace y=0) :
    tracePairing y (shortRootLinear i t y) = -t ^ 2 * (y.2 2 (7-i)) ^ 2 := by
  rw [tracePairing_shortRootLinear, tracePairing_self, ht,
    quadraticTrace_eq_zero_of_adjoint_eq_zero y ha]
  ring

theorem tracePairing_shortRootLinear_one_ne_zero (i : Fin 8) (y : Carrier K)
    (ha : adjoint y=0) (ht : trace y=0) (hi : y.2 2 (7-i)≠0) :
    tracePairing y (shortRootLinear i 1 y) ≠ 0 := by
  rw [tracePairing_shortRootLinear_white i 1 y ha ht]
  simpa using pow_ne_zero 2 hi

end Atlas.Albert
