import Atlas.LinearGroups.ReeF4.PolynomialExterior
import Atlas.LinearGroups.ReeF4.WeylScalar
import Atlas.LinearGroups.ReeF4.WeylStarData
import Atlas.LinearGroups.ReeF4.ExteriorDomain

/-! The concrete Weyl operators act on the full exterior-kernel star domain. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem weylOperator_polar (g : Fin 2) (u v : TraceZero F) :
    traceZeroPolar (weylOperator g u) (weylOperator g v) = traceZeroPolar u v := by
  fin_cases g
  · exact weylRho_polar u v
  · exact weylSigma_polar u v

theorem weylOperator_cross (g : Fin 2) (u v : TraceZero F) :
    traceZeroCross (weylOperator g u) (weylOperator g v) =
      weylOperator g (traceZeroCross u v) := by
  fin_cases g
  · exact weylRho_cross u v
  · exact weylSigma_cross u v

theorem exteriorPolar_comp_weyl (g : Fin 2) :
    (exteriorPolar (F := F)).comp (exteriorPower.map 2 (weylOperator g).toLinearMap) =
      exteriorPolar := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro m
  change exteriorPolar (exteriorPower.map 2 (weylOperator g).toLinearMap
    (exteriorPower.ιMulti F 2 m)) = exteriorPolar (exteriorPower.ιMulti F 2 m)
  simp [exteriorPolar, exteriorPower.map_apply_ιMulti, polarAlternating,
    weylOperator_polar]

theorem exteriorCross_comp_weyl (g : Fin 2) :
    (exteriorCross (F := F)).comp (exteriorPower.map 2 (weylOperator g).toLinearMap) =
      (weylOperator g).toLinearMap.comp exteriorCross := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro m
  change exteriorCross (exteriorPower.map 2 (weylOperator g).toLinearMap
    (exteriorPower.ιMulti F 2 m)) =
      weylOperator g (exteriorCross (exteriorPower.ιMulti F 2 m))
  simp [exteriorCross, exteriorPower.map_apply_ιMulti, crossAlternating,
    weylOperator_cross]

theorem weylExterior_mem (g : Fin 2) (x : StarCarrier (F := F)) :
    exteriorPower.map 2 (weylOperator g).toLinearMap x.val ∈ StarCarrier (F := F) := by
  have hp := LinearMap.congr_fun (exteriorPolar_comp_weyl (F := F) g) x.val
  have hc := LinearMap.congr_fun (exteriorCross_comp_weyl (F := F) g) x.val
  obtain ⟨hx, hy⟩ := x.property
  change exteriorPolar x.val = 0 at hx
  change exteriorCross x.val = 0 at hy
  constructor
  · change exteriorPolar (exteriorPower.map 2 (weylOperator g).toLinearMap x.val) = 0
    exact hp.trans hx
  · change exteriorCross (exteriorPower.map 2 (weylOperator g).toLinearMap x.val) = 0
    exact hc.trans (by rw [LinearMap.comp_apply, hy, map_zero])

def weylStarLinear (g : Fin 2) : StarCarrier (F := F) →ₗ[F] StarCarrier (F := F) :=
  polynomialStarLinear (F := F) ⟨weylOperator g, weylOperator_mem_polynomialStabilizer g⟩

theorem starDomain_weyl_iff (g : Fin 2) (u v : TraceZero F) :
    StarDomain (weylOperator g u) (weylOperator g v) ↔ StarDomain u v := by
  change (_ = 0 ∧ _ = 0) ↔ (_ = 0 ∧ _ = 0)
  rw [weylOperator_polar, weylOperator_cross]
  constructor
  · rintro ⟨hb, hc⟩
    refine ⟨hb, (weylOperator g).injective ?_⟩
    simpa only [map_zero] using hc
  · rintro ⟨hb, hc⟩
    exact ⟨hb, by rw [hc, map_zero]⟩

theorem weylStarLinear_domainWedge (g : Fin 2) (u v : TraceZero F) (h : StarDomain u v) :
    weylStarLinear g (domainWedge u v h) =
      domainWedge (weylOperator g u) (weylOperator g v)
        ((starDomain_weyl_iff g u v).mpr h) := by
  apply Subtype.ext
  change exteriorPower.map 2 (weylOperator g).toLinearMap (wedge u v) =
    wedge (weylOperator g u) (weylOperator g v)
  simp only [wedge, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

end Atlas.ReeF4
