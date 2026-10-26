import Atlas.LinearGroups.Triality.FoldedRootLaws
import Atlas.LinearGroups.Triality.FoldedCoordinates

noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Additive parameter group embedded in the actual quadratic isometries. -/
def shortRootHom : Multiplicative K →* O_DPlus 4 K where
  toFun a := shortRoot F K a.toAdd
  map_one' := shortRoot_zero F K
  map_mul' a b := shortRoot_add F K a.toAdd b.toAdd

def shortRootSubgroup : Subgroup (O_DPlus 4 K) := (shortRootHom F K).range

theorem card_shortRootSubgroup : Nat.card (shortRootSubgroup F K) = Nat.card K := by
  change Nat.card (Set.range (shortRoot F K)) = Nat.card K
  exact Nat.card_range_of_injective (shortRoot_injective F K)

/-- Additive parameter group embedded in the actual quadratic isometries. -/
def shortNegativeRootHom : Multiplicative K →* O_DPlus 4 K where
  toFun a := shortNegativeRoot F K a.toAdd
  map_one' := shortNegativeRoot_zero F K
  map_mul' a b := shortNegativeRoot_add F K a.toAdd b.toAdd

def shortNegativeRootSubgroup : Subgroup (O_DPlus 4 K) := (shortNegativeRootHom F K).range

theorem card_shortNegativeRootSubgroup : Nat.card (shortNegativeRootSubgroup F K) = Nat.card K := by
  change Nat.card (Set.range (shortNegativeRoot F K)) = Nat.card K
  exact Nat.card_range_of_injective (shortNegativeRoot_injective F K)

/-- Additive parameter group embedded in the actual quadratic isometries. -/
def longRootHom : Multiplicative F →* O_DPlus 4 K where
  toFun a := longRoot F K a.toAdd
  map_one' := longRoot_zero F K
  map_mul' a b := longRoot_add F K a.toAdd b.toAdd

def longRootSubgroup : Subgroup (O_DPlus 4 K) := (longRootHom F K).range

theorem card_longRootSubgroup : Nat.card (longRootSubgroup F K) = Nat.card F := by
  change Nat.card (Set.range (longRoot F K)) = Nat.card F
  exact Nat.card_range_of_injective (longRoot_injective F K)

/-- Additive parameter group embedded in the actual quadratic isometries. -/
def longNegativeRootHom : Multiplicative F →* O_DPlus 4 K where
  toFun a := longNegativeRoot F K a.toAdd
  map_one' := longNegativeRoot_zero F K
  map_mul' a b := longNegativeRoot_add F K a.toAdd b.toAdd

def longNegativeRootSubgroup : Subgroup (O_DPlus 4 K) := (longNegativeRootHom F K).range

theorem card_longNegativeRootSubgroup : Nat.card (longNegativeRootSubgroup F K) = Nat.card F := by
  change Nat.card (Set.range (longNegativeRoot F K)) = Nat.card F
  exact Nat.card_range_of_injective (longNegativeRoot_injective F K)

theorem card_shortRootSubgroup_cubic (hdeg : Module.finrank F K = 3) :
    Nat.card (shortRootSubgroup F K) = Nat.card F ^ 3 := by
  rw [card_shortRootSubgroup, FiniteCubic.card_extension hdeg]

theorem card_shortNegativeRootSubgroup_cubic (hdeg : Module.finrank F K = 3) :
    Nat.card (shortNegativeRootSubgroup F K) = Nat.card F ^ 3 := by
  rw [card_shortNegativeRootSubgroup, FiniteCubic.card_extension hdeg]

end Atlas.Triality
