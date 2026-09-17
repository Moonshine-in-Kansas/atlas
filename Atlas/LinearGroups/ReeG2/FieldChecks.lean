import Atlas.FieldTheory.ReeTitsAutomorphism
import Mathlib.FieldTheory.Finite.GaloisField

/-! Canonical-field specializations of the uniform field-twist identities. -/
noncomputable section
namespace Atlas.ReeG2

theorem parameters27 : Parameters (GaloisField 3 3) 1 := by
  constructor
  · omega
  · simpa using GaloisField.card 3 3 (by omega)

theorem parameters243 : Parameters (GaloisField 3 5) 2 := by
  constructor
  · omega
  · simpa using GaloisField.card 3 5 (by omega)

theorem sigma_square27 (x : GaloisField 3 3) : sigma _ 1 (sigma _ 1 x) = x ^ 3 :=
  sigma_square parameters27.cardinality x

theorem sigma_square243 (x : GaloisField 3 5) : sigma _ 2 (sigma _ 2 x) = x ^ 3 :=
  sigma_square parameters243.cardinality x
end Atlas.ReeG2
