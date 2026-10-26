import Atlas.Algebra.Albert.Cubic
import Atlas.Algebra.SplitOctonion.TraceIdentities

set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Atlas.Albert
variable {F : Type*} [CommRing F]

def tracePairing (x y : Carrier F) : F :=
  trace x * trace y - (quadraticTrace (x + y) - quadraticTrace x - quadraticTrace y)

def adjoint (x : Carrier F) : Carrier F :=
  (![x.1 1 * x.1 2 - SplitOctonion.norm (x.2 0),
     x.1 2 * x.1 0 - SplitOctonion.norm (x.2 1),
     x.1 0 * x.1 1 - SplitOctonion.norm (x.2 2)],
   ![SplitOctonion.conjugate (SplitOctonion.mul (x.2 1) (x.2 2)) - x.1 0 • x.2 0,
     SplitOctonion.conjugate (SplitOctonion.mul (x.2 2) (x.2 0)) - x.1 1 • x.2 1,
     SplitOctonion.conjugate (SplitOctonion.mul (x.2 0) (x.2 1)) - x.1 2 • x.2 2])

def cross (x y : Carrier F) : Carrier F := adjoint (x + y) - adjoint x - adjoint y

theorem tracePairing_comm (x y : Carrier F) : tracePairing x y = tracePairing y x := by
  simp only [tracePairing, add_comm x y]; ring

theorem adjoint_smul (t : F) (x : Carrier F) :
    adjoint (t • x) = t ^ 2 • adjoint x := by
  apply Prod.ext
  · funext i; fin_cases i <;>
      simp [Matrix.vecHead, Matrix.vecTail, adjoint, SplitOctonion.norm] <;> ring
  · funext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, adjoint, SplitOctonion.conjugate, SplitOctonion.mul,
        SplitOctonion.trace, SplitOctonion.unit] <;> ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem adjoint_adjoint (x : Carrier F) : adjoint (adjoint x) = norm x • x := by
  apply Prod.ext
  · funext i; fin_cases i <;>
      simp [Matrix.vecHead, Matrix.vecTail, adjoint, norm, SplitOctonion.norm, SplitOctonion.mul,
        SplitOctonion.conjugate, SplitOctonion.trace, SplitOctonion.unit] <;> ring
  · funext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, adjoint, norm, SplitOctonion.norm, SplitOctonion.mul,
        SplitOctonion.conjugate, SplitOctonion.trace, SplitOctonion.unit] <;> ring

set_option maxHeartbeats 800000 in
theorem norm_add_smul (t : F) (x y : Carrier F) :
    norm (x + t • y) = norm x + t * tracePairing (adjoint x) y +
      t ^ 2 * tracePairing x (adjoint y) + t ^ 3 * norm y := by
  simp [Matrix.vecHead, Matrix.vecTail, norm, tracePairing, trace, quadraticTrace, adjoint, SplitOctonion.norm,
    SplitOctonion.mul, SplitOctonion.conjugate, SplitOctonion.trace, SplitOctonion.unit]
  ring

end Atlas.Albert
