import Atlas.LinearGroups.Chevalley.RootData.FiniteRootDatum
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! Integer coroot-coordinate maps for nonsimply-laced data. -/

namespace Atlas.Chevalley.SmallExceptionalData
open FiniteRootDatum

def corootMap {r : ℕ} (C : Matrix (Fin r) (Fin r) ℤ) :
    Lattice r →ₗ[ℤ] Module.Dual ℤ (Lattice r) :=
  (dotProductEquiv ℤ (Fin r)).toLinearMap.comp (Matrix.mulVecLin C)

theorem corootMap_injective {r : ℕ} (C : Matrix (Fin r) (Fin r) ℤ)
    (hC : C.det ≠ 0) : Function.Injective (corootMap C) :=
  (dotProductEquiv ℤ (Fin r)).injective.comp
    (Matrix.mulVec_injective_of_det_ne_zero hC)

theorem corootMap_single {r : ℕ} (C : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) :
    corootMap C (Pi.single j 1) (Pi.single i 1) = C i j := by
  simp [corootMap, dotProductEquiv]

end Atlas.Chevalley.SmallExceptionalData
