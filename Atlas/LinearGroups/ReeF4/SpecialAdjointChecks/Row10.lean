import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row09

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
theorem rawStar_adjoint_root9_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 0 7 = 0 := by
  rw [specialAdjoint9_actual]
  exact rawStar_specialAdjoint9_zero u v h
end Atlas.ReeF4
