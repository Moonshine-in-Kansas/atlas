import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import Atlas.LinearGroups.PSLFieldTransport

namespace Atlas.Comparisons.Exceptional.Nine
/-- The existing mathlib quadratic-algebra model supplies coordinates, not new arithmetic. -/
abbrev F := QuadraticAlgebra (ZMod 3) 2 0
instance nineCoordinateIrreducible : Fact (∀ r : ZMod 3, r^2 ≠ 2+0*r) := ⟨by decide⟩
instance nineCoordinateFintype : Fintype F :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3) (QuadraticAlgebra.equivProd 2 0).symm

theorem card : Nat.card F = 9 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_congr (QuadraticAlgebra.equivProd 2 0),Fintype.card_prod]
  norm_num

def omega : F := QuadraticAlgebra.omega
noncomputable def fieldEquiv {K : Type*} [Field K] [Finite K] (h : Nat.card K = 9) : K ≃+* F := by
  letI := Fintype.ofFinite K
  exact FiniteField.ringEquivOfCardEq (by simpa only [←Nat.card_eq_fintype_card] using h.trans card.symm)
end Atlas.Comparisons.Exceptional.Nine
