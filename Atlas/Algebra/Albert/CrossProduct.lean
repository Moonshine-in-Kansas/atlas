import Atlas.Algebra.Albert.TracePairing

/-! Characteristic-independent bilinear cross product of the split Albert space. -/
set_option maxRecDepth 4096
namespace Atlas.Albert
variable {F : Type*} [CommRing F]

theorem cross_comm (x y : Carrier F) : cross x y = cross y x := by
  simp only [cross, add_comm x y]
  abel

set_option maxHeartbeats 4000000 in
theorem cross_add_left (x y z : Carrier F) :
    cross (x + y) z = cross x z + cross y z := by
  apply Prod.ext
  · funext i; fin_cases i <;>
      simp [Matrix.vecHead, Matrix.vecTail, cross, adjoint, SplitOctonion.norm] <;> ring
  · funext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, cross, adjoint, SplitOctonion.conjugate, SplitOctonion.mul,
        SplitOctonion.trace, SplitOctonion.unit] <;> ring

theorem cross_add_right (x y z : Carrier F) :
    cross x (y + z) = cross x y + cross x z := by
  simpa only [cross_comm] using cross_add_left y z x

set_option maxHeartbeats 4000000 in
theorem cross_smul_left (t : F) (x y : Carrier F) :
    cross (t • x) y = t • cross x y := by
  apply Prod.ext
  · funext i; fin_cases i <;>
      simp [Matrix.vecHead, Matrix.vecTail, cross, adjoint, SplitOctonion.norm] <;> ring
  · funext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, cross, adjoint, SplitOctonion.conjugate, SplitOctonion.mul,
        SplitOctonion.trace, SplitOctonion.unit] <;> ring

theorem cross_smul_right (t : F) (x y : Carrier F) :
    cross x (t • y) = t • cross x y := by
  simpa only [cross_comm] using cross_smul_left t y x

def crossBilinear : Carrier F →ₗ[F] Carrier F →ₗ[F] Carrier F where
  toFun x :=
    { toFun := cross x
      map_add' := cross_add_right x
      map_smul' := fun t y => cross_smul_right t x y }
  map_add' x y := by apply LinearMap.ext; intro z; exact cross_add_left x y z
  map_smul' t x := by apply LinearMap.ext; intro y; exact cross_smul_left t x y

theorem crossBilinear_apply (x y : Carrier F) : crossBilinear x y = cross x y := rfl

theorem trace_adjoint (x : Carrier F) : trace (adjoint x) = quadraticTrace x := by
  simp [Matrix.vecHead, Matrix.vecTail, trace, adjoint, quadraticTrace]; ring

theorem adjoint_unit : adjoint (unit : Carrier F) = unit := by
  apply Prod.ext
  · funext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, adjoint, unit, SplitOctonion.norm]
  · funext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, adjoint, unit, SplitOctonion.conjugate, SplitOctonion.mul,
        SplitOctonion.trace, SplitOctonion.unit]

set_option maxHeartbeats 800000 in
theorem cross_unit (x : Carrier F) : cross x unit = trace x • unit - x := by
  apply Prod.ext
  · funext i; fin_cases i <;>
      simp [Matrix.vecHead, Matrix.vecTail, cross, adjoint, trace, unit, SplitOctonion.norm] <;> ring
  · funext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, cross, adjoint, trace, unit, SplitOctonion.conjugate, SplitOctonion.mul,
        SplitOctonion.trace, SplitOctonion.unit] <;> ring

theorem unit_cross (x : Carrier F) : cross unit x = trace x • unit - x := by
  rw [cross_comm, cross_unit]

theorem trace_cross (x y : Carrier F) :
    trace (cross x y) = trace x * trace y - tracePairing x y := by
  simp [Matrix.vecHead, Matrix.vecTail, cross, tracePairing, trace, adjoint, quadraticTrace]; ring

theorem tracePairing_unit (x : Carrier F) : tracePairing x unit = trace x := by
  simp [Matrix.vecHead, Matrix.vecTail, tracePairing, trace, quadraticTrace, unit, SplitOctonion.norm]; ring

theorem tracePairing_coordinates (x y : Carrier F) :
    tracePairing x y = (∑ i : Fin 3, x.1 i * y.1 i) +
      ∑ i : Fin 3, ∑ j : Fin 8, x.2 i j * y.2 i (7 - j) := by
  simp [tracePairing, trace, quadraticTrace, SplitOctonion.norm, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 1600000 in
/-- The cubic polarization is symmetric without dividing by two or three. -/
theorem tracePairing_cross (x y z : Carrier F) :
    tracePairing (cross x y) z = tracePairing x (cross y z) := by
  rw [tracePairing_coordinates, tracePairing_coordinates]
  simp [Matrix.vecHead, Matrix.vecTail, cross, adjoint, SplitOctonion.norm,
    SplitOctonion.conjugate, SplitOctonion.mul, SplitOctonion.trace, SplitOctonion.unit,
    Fin.sum_univ_succ]
  ring

end Atlas.Albert
