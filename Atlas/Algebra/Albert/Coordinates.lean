import Atlas.Algebra.SplitOctonion.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The marked split Albert space. The three octonion coordinates use the
existing integral split multiplication; no associative octonion algebra is assumed. -/
namespace Atlas.Albert

abbrev Carrier (F : Type*) := (Fin 3 → F) × (Fin 3 → SplitOctonion.Carrier F)
abbrev Coordinate := Fin 3 ⊕ (Fin 3 × Fin 8)

variable {F : Type*} [CommRing F]

def unit : Carrier F := (fun _ => 1, fun _ => 0)
def trace (x : Carrier F) : F := x.1 0 + x.1 1 + x.1 2
def quadraticTrace (x : Carrier F) : F :=
  x.1 0 * x.1 1 + x.1 1 * x.1 2 + x.1 2 * x.1 0 -
  SplitOctonion.norm (x.2 0) - SplitOctonion.norm (x.2 1) -
  SplitOctonion.norm (x.2 2)
def norm (x : Carrier F) : F :=
  x.1 0 * x.1 1 * x.1 2 - x.1 0 * SplitOctonion.norm (x.2 0) -
  x.1 1 * SplitOctonion.norm (x.2 1) - x.1 2 * SplitOctonion.norm (x.2 2) +
  SplitOctonion.trace (SplitOctonion.mul (SplitOctonion.mul (x.2 0) (x.2 1)) (x.2 2))

def coordinateEquiv : Carrier F ≃ₗ[F] (Coordinate → F) where
  toFun x := Sum.elim x.1 (fun i => x.2 i.1 i.2)
  invFun x := (fun i => x (.inl i), fun i j => x (.inr (i,j)))
  left_inv _ := rfl
  right_inv x := by funext i; cases i <;> rfl
  map_add' _ _ := by funext i; cases i <;> rfl
  map_smul' _ _ := by funext i; cases i <;> rfl

theorem norm_unit : norm (unit : Carrier F) = 1 := by
  simp [norm, unit, SplitOctonion.norm, SplitOctonion.trace, SplitOctonion.mul]

theorem carrier_finrank {K : Type*} [Field K] : Module.finrank K (Carrier K) = 27 := by
  rw [(coordinateEquiv (F := K)).finrank_eq]
  simp [Coordinate]

end Atlas.Albert
