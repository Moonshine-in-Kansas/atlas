import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! Distinct coordinate lines remain distinct over any nonzero commutative ring.
The coefficient of each vector is a unit; no field or characteristic assumption
is needed. This helper has no root-system or group-construction dependency. -/

namespace Atlas.LinearAlgebra

variable {R δ : Type*} [CommRing R] [Nontrivial R] [DecidableEq δ]

theorem unit_smul_single_index_unique {j k : δ} (a c : Rˣ)
    (h : a.val • (Pi.single j 1 : δ → R) =
      c.val • (Pi.single k 1 : δ → R)) : j = k := by
  by_contra hjk
  have hs := congrFun h j
  have ha : a.val = 0 := by
    simpa [Pi.smul_apply, smul_eq_mul, Pi.single_apply, hjk, Ne.symm hjk] using hs
  exact a.ne_zero ha

end Atlas.LinearAlgebra
