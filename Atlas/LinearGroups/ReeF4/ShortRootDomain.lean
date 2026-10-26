import Atlas.LinearGroups.ReeF4.ShortRootOrder
import Atlas.LinearGroups.ReeF4.ShortRootForms
import Atlas.LinearGroups.ReeF4.ShortRootCoordinateComparison
import Atlas.LinearGroups.ReeF4.StarDomain

/-! The source short-root operator preserves the actual Albert forms and
the admissible pair domain, uniformly in characteristic two. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem shortRootLinear_quadratic (w : TraceZero F) :
    traceZeroQuadratic (shortRootLinear w) = traceZeroQuadratic w := by
  rw [← shortRootCoordinateLinear_eq]
  exact shortRootFormula_quadratic w.val

theorem shortRootLinear_cubic (w : TraceZero F) :
    traceZeroCubic (shortRootLinear w) = traceZeroCubic w := by
  rw [← shortRootCoordinateLinear_eq]
  exact shortRootFormula_norm w.val

theorem shortRootLinear_polar (u v : TraceZero F) :
    traceZeroPolar (shortRootLinear u) (shortRootLinear v) = traceZeroPolar u v :=
  traceZeroPolar_of_quadratic (shortRootEquiv (F := F)) shortRootLinear_quadratic u v

theorem shortRootLinear_cross (u v : TraceZero F) :
    traceZeroCross (shortRootLinear u) (shortRootLinear v) =
      shortRootLinear (traceZeroCross u v) :=
  traceZeroCross_of_forms (shortRootEquiv (F := F)) shortRootLinear_quadratic
    shortRootLinear_cubic u v

theorem starDomain_shortRoot_iff (u v : TraceZero F) :
    StarDomain (shortRootLinear u) (shortRootLinear v) ↔ StarDomain u v := by
  change (_ = 0 ∧ _ = 0) ↔ (_ = 0 ∧ _ = 0)
  rw [shortRootLinear_polar, shortRootLinear_cross]
  constructor
  · rintro ⟨hb, hc⟩
    refine ⟨hb, (shortRootEquiv (F := F)).injective ?_⟩
    change shortRootLinear (traceZeroCross u v) = shortRootLinear (0 : TraceZero F)
    simpa only [map_zero] using hc
  · rintro ⟨hb, hc⟩
    exact ⟨hb, by rw [hc, map_zero]⟩

end Atlas.ReeF4
