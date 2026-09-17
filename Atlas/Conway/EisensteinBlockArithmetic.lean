import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Atlas.Conway
open scoped BigOperators

/-- The twelve proposed nontrivial subdegrees, with repeated values retained.
This definition alone makes no orbit assertion. -/
def eisensteinNontrivialSubdegree : Fin 12 → ℕ :=
  ![165, 891, 2673, 2673, 2916, 16038, 16038, 17820, 40095, 40095, 40095, 53460]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Arithmetic obstruction for the prescribed subdegrees. Application to blocks
requires a separate proof that these are the actual stabilizer orbits. -/
theorem eisenstein_subdegree_block_arithmetic (S : Finset (Fin 12))
    (hd : (1 + ∑ i ∈ S, eisensteinNontrivialSubdegree i) ∣ 232960) :
    S = ∅ ∨ S = Finset.univ := by
  revert hd S
  decide +kernel

end Atlas.Conway
