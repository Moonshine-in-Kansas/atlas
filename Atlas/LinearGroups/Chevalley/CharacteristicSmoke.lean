import Atlas.LinearGroups.Chevalley.Integral.GeckExponential
import Atlas.LinearGroups.Chevalley.RootData.A
import Atlas.LinearGroups.Chevalley.RootData.E6
import Atlas.LinearGroups.Chevalley.RootData.ClassicalBasesBC
import Mathlib.Data.ZMod.Basic

/-! Construction smoke tests at the two bad primes. These specialize the
integral construction, not a good-characteristic exponential formula. -/
namespace Atlas.Chevalley.CharacteristicSmoke
open Integral
noncomputable local instance : Fintype E6Data.Root := Fintype.ofFinite _
noncomputable local instance : DecidableEq (ClassicalData.BRoot 3) := Classical.decEq _

theorem typeA3_binary_root_faithful (i : Fin 3) :
    Function.Injective
      (raisingRootElement (TypeAData.pairing 4) (TypeAData.base 3) (ZMod 2)
        (TypeAData.baseIndexEquiv 3 i)) :=
  raisingRootElement_injective _ _ _ _

theorem typeA3_ternary_root_faithful (i : Fin 3) :
    Function.Injective
      (loweringRootElement (TypeAData.pairing 4) (TypeAData.base 3) (ZMod 3)
        (TypeAData.baseIndexEquiv 3 i)) :=
  loweringRootElement_injective _ _ _ _

theorem e6_binary_root_faithful (i : Fin 6) :
    Function.Injective
      (raisingRootElement E6Data.pairing E6Data.base (ZMod 2)
        (E6Data.baseIndexEquiv i)) :=
  raisingRootElement_injective _ _ _ _

theorem e6_ternary_root_faithful (i : Fin 6) :
    Function.Injective
      (loweringRootElement E6Data.pairing E6Data.base (ZMod 3)
        (E6Data.baseIndexEquiv i)) :=
  loweringRootElement_injective _ _ _ _

theorem typeB3_binary_root_faithful (i : Fin 3) :
    Function.Injective
      (raisingRootElement (ClassicalData.pairingB 3) (ClassicalData.baseB 2) (ZMod 2)
        (ClassicalData.baseBIndexEquiv 2 i)) :=
  raisingRootElement_injective _ _ _ _

theorem typeC3_binary_root_faithful (i : Fin 3) :
    Function.Injective
      (loweringRootElement (ClassicalData.pairingC 3) (ClassicalData.baseC 2) (ZMod 2)
        (ClassicalData.baseCIndexEquiv 2 i)) :=
  loweringRootElement_injective _ _ _ _

end Atlas.Chevalley.CharacteristicSmoke
