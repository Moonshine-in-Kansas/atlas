import Atlas.LinearGroups.ReeF4.WeylStarData

/-! All fifty-two marked Weyl images, certified in the prime field and
transported uniformly to every characteristic-two coefficient ring. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem weylOperator_support_binary : ∀ (g : Fin 2) (i : TraceZeroCoordinate),
    weylOperator (F := ZMod 2) g (starMarkedVector i) =
      ((weylSupport g i).map starMarkedVector).sum := by
  intro g i
  fin_cases g <;> fin_cases i <;> decide

theorem weylOperator_support (g : Fin 2) (i : TraceZeroCoordinate) :
    weylOperator (F := F) g (starMarkedVector i) =
      ((weylSupport g i).map starMarkedVector).sum := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg (traceZeroScalarMap f) (weylOperator_support_binary g i)
  simp only [map_list_sum, List.map_map, Function.comp_def,
    traceZeroScalarMap_apply, weylOperator_map, starMarkedVector_map] at h
  exact h

end Atlas.ReeF4
