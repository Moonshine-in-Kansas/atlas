import Atlas.LinearGroups.ReeF4.LongRootDomain
import Atlas.LinearGroups.ReeF4.ExteriorDomain

/-! The actual long-root involution acts on the whole exterior-kernel domain.
This does not yet assert preservation of the candidate star map. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem exteriorPolar_comp_longRoot :
    (exteriorPolar (F := F)).comp (exteriorPower.map 2 longRootLinear) =
      exteriorPolar := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro m
  change exteriorPolar (exteriorPower.map 2 longRootLinear
    (exteriorPower.ιMulti F 2 m)) = exteriorPolar (exteriorPower.ιMulti F 2 m)
  simp [exteriorPolar, exteriorPower.map_apply_ιMulti, polarAlternating,
    longRootLinear_polar]

theorem exteriorCross_comp_longRoot :
    (exteriorCross (F := F)).comp (exteriorPower.map 2 longRootLinear) =
      longRootLinear.comp exteriorCross := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro m
  change exteriorCross (exteriorPower.map 2 longRootLinear
    (exteriorPower.ιMulti F 2 m)) = longRootLinear (exteriorCross (exteriorPower.ιMulti F 2 m))
  simp [exteriorCross, exteriorPower.map_apply_ιMulti, crossAlternating,
    longRootLinear_cross]

theorem longRootExterior_mem (x : StarCarrier (F := F)) :
    exteriorPower.map 2 longRootLinear x.val ∈ StarCarrier (F := F) := by
  have hp := LinearMap.congr_fun (exteriorPolar_comp_longRoot (F := F)) x.val
  have hc := LinearMap.congr_fun (exteriorCross_comp_longRoot (F := F)) x.val
  obtain ⟨hx, hy⟩ := x.property
  change exteriorPolar x.val = 0 at hx
  change exteriorCross x.val = 0 at hy
  constructor
  · change exteriorPolar (exteriorPower.map 2 longRootLinear x.val) = 0
    exact hp.trans hx
  · change exteriorCross (exteriorPower.map 2 longRootLinear x.val) = 0
    exact hc.trans (by rw [LinearMap.comp_apply, hy, map_zero])

def longRootStarLinear : StarCarrier (F := F) →ₗ[F] StarCarrier (F := F) :=
  ((exteriorPower.map 2 (longRootLinear (F := F))).comp
    (StarCarrier (F := F)).subtype).codRestrict _ (longRootExterior_mem (F := F))

theorem longRootStarLinear_square :
    (longRootStarLinear (F := F)).comp longRootStarLinear = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change exteriorPower.map 2 longRootLinear
    (exteriorPower.map 2 longRootLinear x.val) = x.val
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, longRootLinear_square,
    exteriorPower.map_id]
  rfl

def longRootStarEquiv : StarCarrier (F := F) ≃ₗ[F] StarCarrier (F := F) :=
  LinearEquiv.ofInvolutive (longRootStarLinear (F := F))
    (fun x => LinearMap.congr_fun (longRootStarLinear_square (F := F)) x)

theorem longRootStarLinear_domainWedge (u v : TraceZero F) (h : StarDomain u v) :
    longRootStarLinear (domainWedge u v h) =
      domainWedge (longRootLinear u) (longRootLinear v)
        ((starDomain_longRoot_iff u v).mpr h) := by
  apply Subtype.ext
  change exteriorPower.map 2 longRootLinear (wedge u v) =
    wedge (longRootLinear u) (longRootLinear v)
  simp only [wedge, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

end Atlas.ReeF4
