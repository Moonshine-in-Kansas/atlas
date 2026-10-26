import Atlas.LinearGroups.ReeF4.SpecialIsotropyCrossChecks.Row24

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem isotropyCross_component25 (x y : Fin 26 → F) :
    isotropyCoordinates (traceZeroCross (isotropyPoint x) (isotropyPoint y)) 25 =
      isotropyCross x y 25 := by
  simp [Matrix.vecHead,Matrix.vecTail,isotropyCoordinates,isotropyCross,isotropyPoint,traceZeroCross,traceZeroProjection,
    cross,adjoint,trace,unit,SplitOctonion.mul,SplitOctonion.norm,SplitOctonion.conjugate,
    SplitOctonion.trace,SplitOctonion.unit,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

end Atlas.ReeF4
