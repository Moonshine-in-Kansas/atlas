import Atlas.Codes.TernaryBinaryComparisonData
import Atlas.Mathieu.Mathieu12Witt

namespace Atlas.Codes

def ternaryBinaryDodecadSet : Finset Omega :=
  Finset.univ.filter (fun p => p.2 = 1 ∨ p.2 = 3)

theorem ternaryBinaryDodecad_support : support ternaryBinaryDodecadWord =
    ternaryBinaryDodecadSet := by
  ext p
  simp only [support, ternaryBinaryDodecadSet, Finset.mem_filter, Finset.mem_univ, true_and]
  revert p
  decide +kernel

theorem ternaryBinaryDodecadSet_mem : ternaryBinaryDodecadSet ∈ dodecads := by
  apply (dodecads_mem _).mpr
  exact ⟨⟨ternaryBinaryDodecadWord, ternaryBinaryDodecadWord_mem⟩,
    by decide +kernel, ternaryBinaryDodecad_support⟩

/-- A concrete dodecad of the retained binary Golay code. -/
def ternaryComparisonDodecad : Dodecad :=
  ⟨ternaryBinaryDodecadSet, ternaryBinaryDodecadSet_mem⟩

theorem ternaryBinaryPosition_mem (i : Fin 12) :
    ternaryBinaryPosition i ∈ ternaryComparisonDodecad.val := by
  change ternaryBinaryPosition i ∈ ternaryBinaryDodecadSet
  revert i; decide

def ternaryWittPoint (i : Fin 12) : Mathieu12Points ternaryComparisonDodecad :=
  ⟨ternaryBinaryPosition i, ternaryBinaryPosition_mem i⟩

theorem ternaryWittPoint_bijective : Function.Bijective ternaryWittPoint := by
  constructor
  · intro i j h
    exact ternaryBinaryPosition_injective (congrArg Subtype.val h)
  · intro p
    have hf : ∀ q : Omega, q ∈ ternaryBinaryDodecadSet → ∃ i, ternaryBinaryPosition i = q := by
      decide
    obtain ⟨i, hi⟩ := hf p.val p.prop
    exact ⟨i, Subtype.ext hi⟩

/-- Actual coordinate bijection; no identification from design parameters. -/
noncomputable def ternaryWittCoordinates : Fin 12 ≃ Mathieu12Points ternaryComparisonDodecad :=
  Equiv.ofBijective ternaryWittPoint ternaryWittPoint_bijective

@[simp] theorem ternaryWittCoordinates_val (i : Fin 12) :
    (ternaryWittCoordinates i).val = ternaryBinaryPosition i := rfl

end Atlas.Codes
