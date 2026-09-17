import Atlas.Fischer.SignedMonomialGeometry
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Basic

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem signedCoordinate_linearIndependent {ι : Type*} (j : ι → CoordinateIndex)
    (hj : Function.Injective j) (s : ι → Bit) :
    LinearIndependent Scalar (fun i => parkerScalarSign (s i) • coordinateVector (j i)) := by
  have hs (i : ι) : parkerScalarSign (s i) ≠ 0 := by
    intro h
    have he := parkerScalarSign_square (s i)
    rw [h,zero_mul] at he
    exact zero_ne_one he
  let w : ι → Scalarˣ := fun i => Units.mk0 _ (hs i)
  convert ((Pi.basisFun Scalar CoordinateIndex).linearIndependent.comp j hj).units_smul w using 1
  funext i
  simp [w,coordinateVector,Pi.basisFun_apply]

end Atlas.Fischer
