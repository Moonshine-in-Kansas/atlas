import Atlas.Rudvalis.SeedResidueSpanning

/-! Nineteen explicit pivot residues spanning the actual binary residue code. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def seedPivotIndex : Fin 19 → Fin 112 :=
  ![0,1,2,3,4,5,7,8,9,11,13,16,17,19,21,25,32,33,48]

noncomputable def seedBasisResidue (i : Fin 19) : BinaryWord :=
  seedOrbitResidue (seedOrbitEnumerate (seedPivotIndex i))

theorem seedSpanWitness_pivots (i : Fin 19) (n : Fin 112) (hn : n∈seedSpanWitness i) :
    ∃ j : Fin 19, seedPivotIndex j=n := by
  decide +kernel +revert

theorem binaryGenerator_mem_pivotSpan (i : Fin 19) :
    binaryNormalMap (binaryParameterGenerator (seedGeneratorIndex i)) ∈
      Submodule.span Bit (Set.range seedBasisResidue) := by
  rw [← seedSpanWitness_parameters,map_sum]
  apply Submodule.sum_mem
  intro n hn
  obtain ⟨j,rfl⟩ := seedSpanWitness_pivots i n hn
  rw [← seedOrbitResidue_parameters]
  exact Submodule.subset_span ⟨j,rfl⟩

theorem seedBasisResidue_span :
    Submodule.span Bit (Set.range seedBasisResidue)=binaryResidue := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨i,rfl⟩
    exact seedOrbitResidue_mem _
  · rintro w ⟨a,rfl⟩
    rw [binaryNormalMap_expansion]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    obtain ⟨j,rfl⟩ := seedGeneratorIndex_surjective i
    exact binaryGenerator_mem_pivotSpan j

end Atlas.Rudvalis
