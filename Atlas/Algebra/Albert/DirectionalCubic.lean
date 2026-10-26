import Atlas.Algebra.Albert.RankOne
import Atlas.Algebra.Albert.ScalarMap
import Mathlib.Algebra.Polynomial.Coeff

noncomputable section
namespace Atlas.Albert
variable {F : Type*} [CommRing F]

set_option maxHeartbeats 800000 in
theorem adjoint_map {S : Type*} [CommRing S] (f : F →+* S) (x : Carrier F) :
    adjoint (map f x) = map f (adjoint x) := by
  apply Prod.ext
  · funext i; fin_cases i <;>
      simp [adjoint, map, SplitOctonion.norm]
  · funext i j; fin_cases i <;> fin_cases j <;>
      simp [adjoint, map, Matrix.vecHead, Matrix.vecTail, SplitOctonion.conjugate,
        SplitOctonion.mul, SplitOctonion.trace, SplitOctonion.unit]

theorem tracePairing_map {S : Type*} [CommRing S] (f : F →+* S) (x y : Carrier F) :
    tracePairing (map f x) (map f y) = f (tracePairing x y) := by
  simp [tracePairing, ← map_add, trace_map, quadraticTrace_map]

def directionalCubic (x y : Carrier F) : Polynomial F :=
  norm (map (Polynomial.C : F →+* Polynomial F) x + (Polynomial.X : Polynomial F) • map Polynomial.C y)

theorem directionalCubic_expansion (x y : Carrier F) :
    directionalCubic x y = Polynomial.C (norm x) +
      Polynomial.X * Polynomial.C (tracePairing (adjoint x) y) +
      Polynomial.X ^ 2 * Polynomial.C (tracePairing x (adjoint y)) +
      Polynomial.X ^ 3 * Polynomial.C (norm y) := by
  rw [directionalCubic, norm_add_smul]
  simp only [norm_map, adjoint_map, tracePairing_map]

theorem directionalCubic_coeff_one (x y : Carrier F) :
    (directionalCubic x y).coeff 1 = tracePairing (adjoint x) y := by
  rw [directionalCubic_expansion]
  simp [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_X_pow_mul]

theorem adjoint_eq_zero_iff_linear_coeff (x : Carrier F) :
    adjoint x = 0 ↔ ∀ y, (directionalCubic x y).coeff 1 = 0 := by
  simp only [directionalCubic_coeff_one, adjoint_eq_zero_iff_pairing]

end Atlas.Albert
