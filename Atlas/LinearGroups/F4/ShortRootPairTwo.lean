import Atlas.LinearGroups.F4.ShortRoots
namespace Atlas.F4
variable {F : Type*} [Field F]
theorem shortRoot_pair_two_apply (i : Fin 8) (t : F) (x : Atlas.Albert.Carrier F) :
    (shortRoot 2 i t).val x=Atlas.Albert.coordinateCycle (Atlas.Albert.coordinateCycle
      (Atlas.Albert.shortRootLinear i t (Atlas.Albert.coordinateCycle x))) := by
  change Atlas.Albert.coordinateCycle (Atlas.Albert.coordinateCycle
    (Atlas.Albert.shortRootLinear i t (Atlas.Albert.coordinateCycle
      (Atlas.Albert.coordinateCycle (Atlas.Albert.coordinateCycle (Atlas.Albert.coordinateCycle x)))))) = _
  rw [Atlas.Albert.coordinateCycle_three]


end Atlas.F4
