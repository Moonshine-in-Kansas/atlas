import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row17

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
theorem rawStar_adjoint_root17_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 1 7 = 0 := by
  rw [specialAdjoint17_actual]
  exact rawStar_specialAdjoint17_zero u v h
end Atlas.ReeF4
