import Atlas.Rudvalis.QuaternaryCode
import Atlas.Codes.QuaternaryEvenness

namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

-- Only the two literal56-coordinate seeds are evaluated here.
set_option maxRecDepth 8192 in
theorem quaternary_base_seed_weight (x : Fin 2) :
    euclideanWeight (quaternarySeed (0,0,0,x))=16 := by
  unfold euclideanWeight
  rw [← Equiv.sum_comp seedCoordinateEquiv]
  have he (z : SeedCoordinate) : quaternarySeed (0,0,0,x) (seedCoordinateEquiv z)=
      ((signedPositionSign z.2 * seedOrbitOriginal (0,0,0,x)
        (z.1,signedPositionIndex z.2) : ℤ) : ZMod 4) := by
    change ((signedSeedTransport (seedOrbitOriginal (0,0,0,x))
      (seedCoordinateEquiv z) : ℤ) : ZMod 4)=_
    rw [show z=(z.1,z.2) from rfl,signedSeedTransport_apply]
  simp_rw [he]
  clear he
  decide +kernel +revert

theorem quaternaryCode_weight_sixteen_exists :
    ∃ w : QuaternaryWord, w∈quaternaryCode ∧ euclideanWeight w=16 :=
  ⟨quaternarySeed (0,0,0,0),quaternaryCode_seed _,quaternary_base_seed_weight 0⟩

end Atlas.Rudvalis
