import Atlas.LinearGroups.ReeF4.PartialStabilizer
import Atlas.LinearGroups.ReeF4.ExteriorDomain

/-! Every actual polynomial stabilizer acts on the full polar/cross kernel. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
variable (g : traceZeroPolynomialStabilizer (F := F))

theorem exteriorPolar_comp_polynomial :
    (exteriorPolar (F := F)).comp (exteriorPower.map 2 g.val.toLinearMap) =
      exteriorPolar := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro m
  change exteriorPolar (exteriorPower.map 2 g.val.toLinearMap
    (exteriorPower.ιMulti F 2 m)) = exteriorPolar (exteriorPower.ιMulti F 2 m)
  simp [exteriorPolar, exteriorPower.map_apply_ιMulti, polarAlternating,
    traceZeroPolar_of_quadratic g.val (traceZeroStabilizer_quadratic g)]

theorem exteriorCross_comp_polynomial :
    (exteriorCross (F := F)).comp (exteriorPower.map 2 g.val.toLinearMap) =
      g.val.toLinearMap.comp exteriorCross := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro m
  change exteriorCross (exteriorPower.map 2 g.val.toLinearMap
    (exteriorPower.ιMulti F 2 m)) = g.val.toLinearMap (exteriorCross (exteriorPower.ιMulti F 2 m))
  simp [exteriorCross, exteriorPower.map_apply_ιMulti, crossAlternating,
    traceZeroCross_of_forms g.val (traceZeroStabilizer_quadratic g) (traceZeroStabilizer_cubic g)]

theorem polynomialExterior_mem (x : StarCarrier (F := F)) :
    exteriorPower.map 2 g.val.toLinearMap x.val ∈ StarCarrier (F := F) := by
  have hp := LinearMap.congr_fun (exteriorPolar_comp_polynomial g) x.val
  have hc := LinearMap.congr_fun (exteriorCross_comp_polynomial g) x.val
  obtain ⟨hx, hy⟩ := x.property
  change exteriorPolar x.val = 0 at hx
  change exteriorCross x.val = 0 at hy
  constructor
  · change exteriorPolar (exteriorPower.map 2 g.val.toLinearMap x.val) = 0
    exact hp.trans hx
  · change exteriorCross (exteriorPower.map 2 g.val.toLinearMap x.val) = 0
    exact hc.trans (by rw [LinearMap.comp_apply, hy, map_zero])

def polynomialStarLinear : StarCarrier (F := F) →ₗ[F] StarCarrier (F := F) :=
  ((exteriorPower.map 2 (g.val.toLinearMap)).comp
    (StarCarrier (F := F)).subtype).codRestrict _ (polynomialExterior_mem g)

theorem polynomialStarLinear_domainWedge (u v : TraceZero F) (h : StarDomain u v) :
    polynomialStarLinear g (domainWedge u v h) =
      domainWedge (g.val.toLinearMap u) (g.val.toLinearMap v)
        ((starDomain_polynomialStabilizer_iff g u v).mpr h) := by
  apply Subtype.ext
  change exteriorPower.map 2 g.val.toLinearMap (wedge u v) =
    wedge (g.val.toLinearMap u) (g.val.toLinearMap v)
  simp only [wedge, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

end Atlas.ReeF4
