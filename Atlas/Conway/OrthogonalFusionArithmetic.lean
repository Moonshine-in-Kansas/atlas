import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

namespace Atlas.Conway
open scoped BigOperators

/-- Arithmetic only; the five structural orbit identifications are separate obligations. -/
theorem orthogonal_five_sizes_total :
    (∑ i : Fin 5, ![2,924,42240,4928,45056] i) = (93150 : ℕ) := by decide

/-- No nonempty proper union of the five proposed orbit sizes is divisible by 23. -/
theorem orthogonal_five_sizes_fusion (S : Finset (Fin 5))
    (h : 23 ∣ ∑ i ∈ S, (![2,924,42240,4928,45056] i : ℕ)) :
    S = ∅ ∨ S = Finset.univ := by
  have hcheck : ∀ T : Finset (Fin 5),
      23 ∣ ∑ i ∈ T, (![2,924,42240,4928,45056] i : ℕ) → T = ∅ ∨ T = Finset.univ := by
    decide
  exact hcheck S h

end Atlas.Conway
