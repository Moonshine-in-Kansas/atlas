import Atlas.LinearGroups.ReeF4.LongRootForms
import Atlas.LinearGroups.ReeF4.LongRootCoordinateComparison
import Atlas.LinearGroups.ReeF4.StarDomain

/-! The source long-root involution preserves the actual Albert forms and
the admissible pair domain, uniformly in characteristic two. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem longRootLinear_quadratic (w : TraceZero F) :
    traceZeroQuadratic (longRootLinear w) = traceZeroQuadratic w := by
  rw [← longRootCoordinateLinear_eq]
  exact longRootFormula_quadratic w.val

theorem longRootLinear_cubic (w : TraceZero F) :
    traceZeroCubic (longRootLinear w) = traceZeroCubic w := by
  rw [← longRootCoordinateLinear_eq]
  exact longRootFormula_norm w.val

theorem longRootLinear_polar (u v : TraceZero F) :
    traceZeroPolar (longRootLinear u) (longRootLinear v) = traceZeroPolar u v :=
  traceZeroPolar_of_quadratic (longRootEquiv (F := F)) longRootLinear_quadratic u v

theorem longRootLinear_cross (u v : TraceZero F) :
    traceZeroCross (longRootLinear u) (longRootLinear v) =
      longRootLinear (traceZeroCross u v) :=
  traceZeroCross_of_forms (longRootEquiv (F := F)) longRootLinear_quadratic
    longRootLinear_cubic u v

theorem starDomain_longRoot_iff (u v : TraceZero F) :
    StarDomain (longRootLinear u) (longRootLinear v) ↔ StarDomain u v := by
  change (_ = 0 ∧ _ = 0) ↔ (_ = 0 ∧ _ = 0)
  rw [longRootLinear_polar, longRootLinear_cross]
  constructor
  · rintro ⟨hb, hc⟩
    refine ⟨hb, (longRootEquiv (F := F)).injective ?_⟩
    change longRootLinear (traceZeroCross u v) = longRootLinear (0 : TraceZero F)
    simpa only [map_zero] using hc
  · rintro ⟨hb, hc⟩
    exact ⟨hb, by rw [hc, map_zero]⟩

end Atlas.ReeF4
