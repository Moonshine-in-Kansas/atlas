import Atlas.LinearGroups.G2.Primitivity
import Atlas.LinearGroups.G2.IwasawaCriterion
import Atlas.LinearGroups.G2.IwasawaLocal

namespace Atlas.G2
variable {K : Type*} [Field K] [Finite K]

/-- The actual octonion automorphism group is simple over every finite field of size >2. -/
theorem isSimple (hq : 2 < Nat.card K) : IsSimpleGroup (Model K) := by
  letI := singularPoints_primitive (K := K)
  letI := isPerfect hq
  exact (iwasawa hq).isSimpleGroup Group.IsPerfect.commutator_eq_top inferInstance

end Atlas.G2
