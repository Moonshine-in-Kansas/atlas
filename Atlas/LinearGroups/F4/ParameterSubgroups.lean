import Atlas.LinearGroups.F4.ShortRoots
import Atlas.LinearGroups.F4.TorusNorm
import Mathlib.FieldTheory.Finite.Basic

/-! Orders of actual parameter subgroups, independent of the full group order. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

def shortRootHom (pair : Fin 3) (i : Fin 8) : Multiplicative F →* Model F where
  toFun t := shortRoot pair i t.toAdd
  map_one' := shortRoot_zero pair i
  map_mul' s t := shortRoot_add pair i s.toAdd t.toAdd

def shortRootSubgroup (pair : Fin 3) (i : Fin 8) : Subgroup (Model F) :=
  (shortRootHom pair i).range

theorem card_shortRootSubgroup (pair : Fin 3) (i : Fin 8) :
    Nat.card (shortRootSubgroup (F:=F) pair i) = Nat.card F := by
  change Nat.card (Set.range (shortRoot (F:=F) pair i)) = Nat.card F
  exact Nat.card_range_of_injective (shortRoot_injective pair i)

def torusSubgroup : Subgroup (Model F) := (diagonalTorus (F:=F)).range

theorem card_torusSubgroup [Finite F] :
    Nat.card (torusSubgroup (F:=F)) = (Nat.card F - 1)^4 := by
  change Nat.card (Set.range (diagonalTorus (F:=F))) = _
  rw [Nat.card_range_of_injective diagonalTorus_injective]
  simp [TorusParameters,Nat.card_fun,Nat.card_units]

end Atlas.F4
