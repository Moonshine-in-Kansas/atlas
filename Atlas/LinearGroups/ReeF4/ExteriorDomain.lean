import Atlas.LinearGroups.ReeF4.StarDomain
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! The exterior-square domain for the partial Ree product. Its two maps come
from the verified alternating forms. The semilinear star map is a separate
construction; no values for it are assumed here. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

private theorem polar_add_right (u v w : TraceZero F) :
    traceZeroPolar u (v+w) = traceZeroPolar u v + traceZeroPolar u w := by
  simpa only [traceZeroPolar_comm] using traceZeroPolar_add_left v w u

private theorem polar_smul_right (a : F) (u v : TraceZero F) :
    traceZeroPolar u (a • v) = a * traceZeroPolar u v := by
  simpa only [traceZeroPolar_comm] using traceZeroPolar_smul_left a v u

private theorem cross_add_right (u v w : TraceZero F) :
    traceZeroCross u (v+w) = traceZeroCross u v + traceZeroCross u w := by
  simpa only [traceZeroCross_comm] using traceZeroCross_add_left v w u

private theorem cross_smul_right (a : F) (u v : TraceZero F) :
    traceZeroCross u (a • v) = a • traceZeroCross u v := by
  simpa only [traceZeroCross_comm] using traceZeroCross_smul_left a v u

def polarAlternating : (TraceZero F) [⋀^Fin 2]→ₗ[F] F where
  toFun v := traceZeroPolar (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp [traceZeroPolar_add_left, polar_add_right]
  map_update_smul' v i a x := by
    fin_cases i <;> simp [traceZeroPolar_smul_left, polar_smul_right]
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all [traceZeroPolar_self]

def crossAlternating : (TraceZero F) [⋀^Fin 2]→ₗ[F] TraceZero F where
  toFun v := traceZeroCross (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp [traceZeroCross_add_left, cross_add_right]
  map_update_smul' v i a x := by
    fin_cases i <;> simp [traceZeroCross_smul_left, cross_smul_right]
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all [traceZeroCross_self]

def exteriorPolar : (⋀[F]^2 (TraceZero F)) →ₗ[F] F :=
  exteriorPower.alternatingMapLinearEquiv polarAlternating

def exteriorCross : (⋀[F]^2 (TraceZero F)) →ₗ[F] TraceZero F :=
  exteriorPower.alternatingMapLinearEquiv crossAlternating

def StarCarrier : Submodule F (⋀[F]^2 (TraceZero F)) :=
  (exteriorPolar (F:=F)).ker ⊓ (exteriorCross (F:=F)).ker

def wedge (u v : TraceZero F) : ⋀[F]^2 (TraceZero F) :=
  exteriorPower.ιMulti F 2 ![u,v]

@[simp] theorem exteriorPolar_wedge (u v : TraceZero F) :
    exteriorPolar (wedge u v) = traceZeroPolar u v := by
  simp [exteriorPolar, wedge, polarAlternating]

@[simp] theorem exteriorCross_wedge (u v : TraceZero F) :
    exteriorCross (wedge u v) = traceZeroCross u v := by
  simp [exteriorCross, wedge, crossAlternating]

theorem wedge_mem_starCarrier_iff (u v : TraceZero F) :
    wedge u v ∈ StarCarrier (F:=F) ↔ StarDomain u v := by
  simp [StarCarrier, StarDomain, LinearMap.mem_ker]

def domainWedge (u v : TraceZero F) (h : StarDomain u v) : StarCarrier (F:=F) :=
  ⟨wedge u v, (wedge_mem_starCarrier_iff u v).mpr h⟩

end Atlas.ReeF4
