import Atlas.Algebra.Albert.ShortRootMaps
import Atlas.Algebra.Albert.ScalarMap

namespace Atlas.Albert
variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem shortRootFormula_map (f : R →+* S) (x : SplitOctonion.Carrier R)
    (y : Carrier R) :
    shortRootFormula (fun i => f (x i)) (map f y) = map f (shortRootFormula x y) := by
  apply Prod.ext
  · funext i; fin_cases i <;>
      simp [Matrix.vecHead, Matrix.vecTail, shortRootFormula, map, SplitOctonion.trace,
        SplitOctonion.conjugate, SplitOctonion.mul, SplitOctonion.unit]
  · funext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, shortRootFormula, map, SplitOctonion.trace,
        SplitOctonion.conjugate, SplitOctonion.mul, SplitOctonion.unit]

set_option maxHeartbeats 800000 in
theorem shortRootLinear_map (f : R →+* S) (i : Fin 8) (t : R) (y : Carrier R) :
    shortRootLinear i (f t) (map f y) = map f (shortRootLinear i t y) := by
  have hp : (fun j => f ((t • SplitOctonion.basisVector i) j)) =
      f t • SplitOctonion.basisVector i := by
    funext j
    by_cases h : j = i <;> simp [SplitOctonion.basisVector, Pi.single_apply, h]
  change shortRootFormula (f t • SplitOctonion.basisVector i) (map f y) =
    map f (shortRootFormula (t • SplitOctonion.basisVector i) y)
  rw [← hp]
  exact shortRootFormula_map f (t • SplitOctonion.basisVector i) y

theorem shortRootEquiv_map (f : R →+* S) (i : Fin 8) (t : R) (y : Carrier R) :
    shortRootEquiv i (f t) (map f y) = map f (shortRootEquiv i t y) :=
  shortRootLinear_map f i t y

end Atlas.Albert
