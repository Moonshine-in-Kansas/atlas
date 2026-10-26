import Atlas.LinearGroups.F4.TorusLongRootBridge
import Atlas.LinearGroups.F4.TorusShortRootMaps
import Atlas.LinearGroups.F4.RootGeneratedElements
import Atlas.LinearGroups.F4.TorusNorm

/-! Actual rank-one root words for the four simple coroots. The two long coroots
are retained: short coroots alone do not generate the full finite-field torus. -/
-- Composite Albert equivalences require extra reduction during kernel checking.
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

def simplePositive (j : Fin 4) (t : F) : Model F :=
  ![longRoot (torusLongLabel 0) t,longRoot (torusLongLabel 2) t,shortRoot 0 3 t,shortRoot 2 3 t] j

def simpleNegative (j : Fin 4) (t : F) : Model F :=
  ![longRoot (torusLongLabel 1) t,longRoot (torusLongLabel 3) t,shortRoot 0 4 t,shortRoot 2 4 t] j

def simpleCorootParameters (j : Fin 4) (a : Fˣ) : TorusParameters F :=
  ![![a^2,a⁻¹,1,1],![a⁻¹,a^2,a⁻¹,1],![1,(a⁻¹)^2,a^2,a⁻¹],![1,1,a⁻¹,a^2]] j

/-- The raw convention has `w(a)=x(a)y(a⁻¹)x(a)`. -/
def simpleCorootWord (j : Fin 4) (a : Fˣ) : Model F :=
  simplePositive j (a : F) * simpleNegative j ((a⁻¹ : Fˣ) : F) *
    simplePositive j (a : F) * simplePositive j (-1) *
      simpleNegative j (-1) * simplePositive j (-1)

def simplePositiveApply (j : Fin 4) (t : F) (x : Atlas.Albert.Carrier F) :
    Atlas.Albert.Carrier F :=
  ![torusLongApply 0 t x,torusLongApply 2 t x,Atlas.Albert.shortRootLinear 3 t x,
    Atlas.Albert.coordinateCycle (Atlas.Albert.coordinateCycle
      (Atlas.Albert.shortRootLinear 3 t (Atlas.Albert.coordinateCycle x)))] j

def simpleNegativeApply (j : Fin 4) (t : F) (x : Atlas.Albert.Carrier F) :
    Atlas.Albert.Carrier F :=
  ![torusLongApply 1 t x,torusLongApply 3 t x,Atlas.Albert.shortRootLinear 4 t x,
    Atlas.Albert.coordinateCycle (Atlas.Albert.coordinateCycle
      (Atlas.Albert.shortRootLinear 4 t (Atlas.Albert.coordinateCycle x)))] j


end Atlas.F4
