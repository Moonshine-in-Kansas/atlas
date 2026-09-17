import Atlas.Lattices.IcosianHermitianIdentities
import Mathlib.Tactic.NoncommRing

namespace Atlas.Lattices
open Atlas.Algebra

/-- The quaternionic reflection associated with a root of Hermitian norm two. -/
def icosianReflection (r v : IcosianRationalCoordinates) : IcosianRationalCoordinates :=
  v-icosianRightMul r (icosianHermitian r v)

theorem icosianReflection_pairing (r v : IcosianRationalCoordinates)
    (hr : icosianHermitian r r=2) :
    icosianHermitian r (icosianReflection r v)= -icosianHermitian r v := by
  simp only [icosianReflection,icosianHermitian_sub_right,
    icosianHermitian_rightMul_right,hr]
  noncomm_ring

theorem icosianReflection_involutive (r : IcosianRationalCoordinates)
    (hr : icosianHermitian r r=2) : Function.Involutive (icosianReflection r) := by
  intro v
  change icosianReflection r v-icosianRightMul r
    (icosianHermitian r (icosianReflection r v))=v
  rw [icosianReflection_pairing r v hr]
  funext i
  simp [icosianReflection,icosianRightMul]

theorem icosianReflection_hermitian (r v w : IcosianRationalCoordinates)
    (hr : icosianHermitian r r=2) :
    icosianHermitian (icosianReflection r v) (icosianReflection r w)=
      icosianHermitian v w := by
  have hv : icosianHermitian v r=star (icosianHermitian r v) :=
    (icosianHermitian_star r v).symm
  simp only [icosianReflection,icosianHermitian_sub_left,icosianHermitian_sub_right,
    icosianHermitian_rightMul_left,icosianHermitian_rightMul_right,hr,hv]
  noncomm_ring

end Atlas.Lattices
