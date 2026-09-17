import Atlas.Fischer.QuinticPointUUU
import Atlas.Fischer.QuinticPointUWW
import Atlas.Fischer.QuinticPointWWW
import Atlas.Fischer.QuinticSymmetry

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem cubicPointPattern_delta (p q r : Omega) :
    cubicPointPattern p q r = -1 + 16 * cubicPointDelta p q r -
      128 * cubicPointDeltaThree p q r := by
  classical
  by_cases hpq : p = q <;> by_cases hqr : q = r <;> by_cases hpr : p = r <;>
    simp_all [cubicPointPattern, cubicPointDelta, cubicPointDeltaThree, eq_comm] <;> norm_num

theorem quinticPointUWW_normalized (p q r : Omega) :
    1024 * (quinticPointUWW p q r + quinticPointUWW q p r + quinticPointUWW r p q) =
      -1485 / 16 + 2640 * cubicPointDelta p q r := by
  rw [quinticPointUWW_three]
  simp only [cubicPointDelta, eq_comm]

/-- All three point-equality cases, uniformly for the actual coordinate indices.
The four source contributions are actual restricted sums of K. -/
theorem coordinateQuintic_points_scaled (p q r : Omega) :
    1024 * coordinateQuintic (.inl p) (.inl q) (.inl r) =
      1002 * cubicPointPattern p q r := by
  calc
    _ = 1024 * quinticPointUUU p q r +
        1024 * (quinticPointUWW p q r + quinticPointUWW q p r + quinticPointUWW r p q) +
          1024 * quinticPointWWW p q r := by
      rw [coordinateQuintic_points_blocks, quinticPointWUW_eq_UWW, quinticPointWWU_eq_UWW]
      ring
    _ = _ := by
      rw [quinticPointUUU_normalized, quinticPointUWW_normalized, quinticPointWWW_source_rows,
        cubicSextetPointContributionOverGamma_eq, cubicTrioPointContributionOverGamma_eq,
        cubicPointPattern_delta]
      ring

theorem coordinateQuintic_points (p q r : Omega) :
    coordinateQuintic (.inl p) (.inl q) (.inl r) =
      (1002 : Scalar) * coordinateCubic (.inl p) (.inl q) (.inl r) := by
  rw [coordinateCubic_points]
  linear_combination (1 / 1024 : Scalar) * coordinateQuintic_points_scaled p q r

end Atlas.Fischer
