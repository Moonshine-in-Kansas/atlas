import Atlas.Fischer.CubicMixedNeighborCounts
import Atlas.Fischer.CubicTriangleAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The actual Type A octad on the two indicated source columns. -/
def countingColumnPairOctad (i j : Fin 6) (hij : i ≠ j) : Octad :=
  countingSourceOctadEquiv (.inl ⟨{i,j},Finset.card_pair hij⟩)

 theorem countingColumnPairOctad_val (i j : Fin 6) (hij : i ≠ j) :
    (countingColumnPairOctad i j hij).val = tetrad (hexPos i) ∪ tetrad (hexPos j) := by
  ext p
  rw [countingColumnPairOctad,countingSourceColumn_membership]
  change (countingPointCoordinates p).2 ∈
    (if (countingPointCoordinates p).1 ∈ ({i,j} : Finset (Fin 6)) then Finset.univ else ∅) ↔ _
  have he (k : Fin 6) : hexIndexEquiv p.1 = k ↔ p.1 = hexPos k := by
    exact ⟨fun h => (hexPos_index p.1).symm.trans (congrArg hexPos h),
      fun h => by simp [h,hexPos]⟩
  by_cases hi : (countingPointCoordinates p).1 ∈ ({i,j} : Finset (Fin 6)) <;>
    simp_all [Finset.mem_union,mem_tetrad,countingPointCoordinates,he]

def countingCanonicalD : Octad := countingColumnPairOctad 0 1 (by decide)
def countingCanonicalSextetE : Octad := countingColumnPairOctad 0 2 (by decide)
def countingCanonicalSextetF : Octad := countingColumnPairOctad 1 2 (by decide)
def countingCanonicalTrioE : Octad := countingColumnPairOctad 2 3 (by decide)
def countingCanonicalTrioF : Octad := countingColumnPairOctad 4 5 (by decide)

 theorem countingColumnPairOctad_apply (i j : HexIndex) (hij : i ≠ j) :
    (countingColumnPairOctad (hexIndexEquiv i) (hexIndexEquiv j)
      (fun h => hij (hexIndexEquiv.injective h))).val = tetrad i ∪ tetrad j := by
  rw [countingColumnPairOctad_val,hexPos_index,hexPos_index]

end Atlas.Fischer
