import Atlas.LinearGroups.Chevalley.RootData.SmallExceptional
import Atlas.LinearGroups.Chevalley.Integral.GeckExponential
import Mathlib.Data.ZMod.Basic

/-! Bad-characteristic specializations of the integral exceptional construction. -/
namespace Atlas.Chevalley.CharacteristicSmoke
open Integral

theorem f4_binary_root_faithful (i : Fin 4) :
    Function.Injective
      (raisingRootElement F4Data.pairing F4Data.base (ZMod 2)
        (F4Data.baseIndexEquiv i)) :=
  raisingRootElement_injective _ _ _ _

theorem g2_ternary_root_faithful (i : Fin 2) :
    Function.Injective
      (loweringRootElement G2Data.pairing G2Data.base (ZMod 3)
        (G2Data.baseIndexEquiv i)) :=
  loweringRootElement_injective _ _ _ _

end Atlas.Chevalley.CharacteristicSmoke
