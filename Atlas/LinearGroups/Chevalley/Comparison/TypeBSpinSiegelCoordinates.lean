import Atlas.LinearGroups.Chevalley.Comparison.TypeBSpinVectorConjugation
import Atlas.LinearGroups.Orthogonal.OddSiegelCoordinates

/-! The gamma coordinate maps are exactly the original odd quadratic Siegel
isometries. This comparison is local and keeps the short-root parameter signs. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeB
open Atlas.BooleanSpin Atlas.Orthogonal
variable (r : ℕ) (F : Type*) [Field F]

theorem longCoordinates_eq_oddLong (i j : Fin r) (hij : i ≠ j) (t : F)
    (v : VectorB r F) :
    longCoordinates r F i j t v = (oddLong r F i j hij t).val v :=
  (oddLong_apply r F i j hij t v).symm

theorem shortUpperCoordinates_eq_oddShortUpper (i : Fin r) (t : F)
    (v : VectorB r F) :
    shortUpperCoordinates r F i t v = (oddShortUpper r F i t).val v :=
  (oddShortUpper_apply r F i t v).symm

theorem shortLowerCoordinates_eq_oddShortLower (i : Fin r) (t : F)
    (v : VectorB r F) :
    shortLowerCoordinates r F i t v = (oddShortLower r F i t).val v :=
  (oddShortLower_apply r F i t v).symm

theorem spinGamma_oddLong (i j : Fin r) (hij : i ≠ j) (t : F)
    (v : VectorB r F) :
    (1+t • (creation F i*annihilation F j))*spinGamma r F v*
      (1-t • (creation F i*annihilation F j)) =
      spinGamma r F ((oddLong r F i j hij t).val v) := by
  rw [← longCoordinates_eq_oddLong]
  exact spinGamma_long r F i j hij t v

theorem spinGamma_oddShortUpper (i : Fin r) (t : F) (v : VectorB r F) :
    (1+t • (creation F i*parity F))*spinGamma r F v*
      (1-t • (creation F i*parity F)) =
      spinGamma r F ((oddShortUpper r F i t).val v) := by
  rw [← shortUpperCoordinates_eq_oddShortUpper]
  exact spinGamma_shortUpper r F i t v

theorem spinGamma_oddShortLower (i : Fin r) (t : F) (v : VectorB r F) :
    (1+t • (parity F*annihilation F i))*spinGamma r F v*
      (1-t • (parity F*annihilation F i)) =
      spinGamma r F ((oddShortLower r F i t).val v) := by
  rw [← shortLowerCoordinates_eq_oddShortLower]
  exact spinGamma_shortLower r F i t v

end Atlas.Chevalley.Comparison.TypeB
