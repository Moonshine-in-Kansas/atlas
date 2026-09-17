import Atlas.Comparisons.Exceptional.DeletedEightSplit
import Atlas.LinearGroups.Orthogonal.Radical

namespace Atlas.Comparisons.Exceptional.DeletedEight
open Atlas.Codes Atlas.Orthogonal

theorem split_polar (x y : D) :
    quotientQuadratic.polarBilin (splitIsometry x) (splitIsometry y) =
      (formD 3 Bit).polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [← map_add splitIsometry, splitIsometry.map_app, splitIsometry.map_app, splitIsometry.map_app]

theorem quotient_polar_separating (x : W) (hx : ∀ y, quotientQuadratic.polarBilin x y = 0) : x = 0 := by
  obtain ⟨v,rfl⟩ := splitIsometry.surjective x
  have hv : v = 0 := polarD_separating v (fun w => by
    rw [← split_polar]
    exact hx (splitIsometry w))
  simp [hv]

theorem quotient_polar_nondegenerate : quotientQuadratic.polarBilin.Nondegenerate := by
  constructor
  · exact quotient_polar_separating
  · intro x hx
    apply quotient_polar_separating x
    intro y
    simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using hx y

end Atlas.Comparisons.Exceptional.DeletedEight

