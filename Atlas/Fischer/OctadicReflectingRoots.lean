import Atlas.Fischer.OctadicAlgebraAutomorphisms
import Atlas.Fischer.ReflectingRoots

namespace Atlas.Fischer
open Atlas.Codes

/-- The intrinsic reflecting-root predicate holds for every actual octadic phase. -/
theorem octadicRoot_phase_isReflectingRoot {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (a : Scalar) (ha : a ^ 3 = 1) :
    IsReflectingRoot (a • octadicRoot Q χ) :=
  octadicRoot_phase_algebra_package Q χ a ha

/-- Every actual octadic character root is reflecting, independently of any ray family. -/
theorem octadicRoot_isReflectingRoot {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) : IsReflectingRoot (octadicRoot Q χ) := by
  simpa only [one_smul] using octadicRoot_phase_isReflectingRoot Q χ 1 (by simp)

end Atlas.Fischer
