import Atlas.LinearGroups.ReeF4.ShortRootDomain
import Atlas.LinearGroups.ReeF4.ExteriorDomain

/-! The actual short-root operator acts on the whole exterior-kernel domain.
This does not yet assert preservation of the candidate star map. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem exteriorPolar_comp_shortRoot :
    (exteriorPolar (F := F)).comp (exteriorPower.map 2 shortRootLinear) =
      exteriorPolar := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro m
  change exteriorPolar (exteriorPower.map 2 shortRootLinear
    (exteriorPower.ιMulti F 2 m)) = exteriorPolar (exteriorPower.ιMulti F 2 m)
  simp [exteriorPolar, exteriorPower.map_apply_ιMulti, polarAlternating,
    shortRootLinear_polar]

theorem exteriorCross_comp_shortRoot :
    (exteriorCross (F := F)).comp (exteriorPower.map 2 shortRootLinear) =
      shortRootLinear.comp exteriorCross := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro m
  change exteriorCross (exteriorPower.map 2 shortRootLinear
    (exteriorPower.ιMulti F 2 m)) = shortRootLinear (exteriorCross (exteriorPower.ιMulti F 2 m))
  simp [exteriorCross, exteriorPower.map_apply_ιMulti, crossAlternating,
    shortRootLinear_cross]

theorem shortRootExterior_mem (x : StarCarrier (F := F)) :
    exteriorPower.map 2 shortRootLinear x.val ∈ StarCarrier (F := F) := by
  have hp := LinearMap.congr_fun (exteriorPolar_comp_shortRoot (F := F)) x.val
  have hc := LinearMap.congr_fun (exteriorCross_comp_shortRoot (F := F)) x.val
  obtain ⟨hx, hy⟩ := x.property
  change exteriorPolar x.val = 0 at hx
  change exteriorCross x.val = 0 at hy
  constructor
  · change exteriorPolar (exteriorPower.map 2 shortRootLinear x.val) = 0
    exact hp.trans hx
  · change exteriorCross (exteriorPower.map 2 shortRootLinear x.val) = 0
    exact hc.trans (by rw [LinearMap.comp_apply, hy, map_zero])

def shortRootStarLinear : StarCarrier (F := F) →ₗ[F] StarCarrier (F := F) :=
  ((exteriorPower.map 2 (shortRootLinear (F := F))).comp
    (StarCarrier (F := F)).subtype).codRestrict _ (shortRootExterior_mem (F := F))

theorem shortRootStarLinear_domainWedge (u v : TraceZero F) (h : StarDomain u v) :
    shortRootStarLinear (domainWedge u v h) =
      domainWedge (shortRootLinear u) (shortRootLinear v)
        ((starDomain_shortRoot_iff u v).mpr h) := by
  apply Subtype.ext
  change exteriorPower.map 2 shortRootLinear (wedge u v) =
    wedge (shortRootLinear u) (shortRootLinear v)
  simp only [wedge, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

end Atlas.ReeF4
