import Atlas.Rudvalis.SeedResidueParameters

namespace Atlas.Rudvalis
open scoped BigOperators

def seedGeneratorIndex (i : Fin 19) : BinaryGeneratorIndex :=
  if h : i.val<7 then .inl (rowLabel (![1,5,6,4,2,0,3] ⟨i.val,h⟩))
  else if i.val<16 then .inr (.inl
    (⟨(i.val-7)/3%3,Nat.mod_lt _ (by decide)⟩,⟨(i.val-7)%3,Nat.mod_lt _ (by decide)⟩))
  else .inr (.inr ⟨(i.val-16)%3,Nat.mod_lt _ (by decide)⟩)

theorem seedGeneratorIndex_surjective : Function.Surjective seedGeneratorIndex := by
  intro t
  rcases t with p | t
  · obtain ⟨r,rfl⟩ := rowEquiv.surjective p
    have h : ∀ r : Fin 7, ∃ i : Fin 19, seedGeneratorIndex i=Sum.inl (rowLabel r) := by
      decide +kernel
    exact h r
  · rcases t with ⟨j,k⟩ | j
    · have h : ∀ j k : Fin 3, ∃ i : Fin 19,
          seedGeneratorIndex i=Sum.inr (Sum.inl (j,k)) := by decide +kernel
      exact h j k
    · have h : ∀ j : Fin 3, ∃ i : Fin 19,
          seedGeneratorIndex i=Sum.inr (Sum.inr j) := by decide +kernel
      exact h j

def seedSpanWitness : Fin 19 → Finset (Fin 112) :=
  ![{0,1,2,5,7,8,13,21,25,32,48},
    {2,5,11,21,25,32,48},
    {0,2,4,5,11,21,25,32,48},
    {2,3,4,5,7,8,9,11,13,21,25,32,48},
    {0,4,7,8,9,21,25,32,48},
    {5,8,11,21,25,32,48},
    {4,5,11,21,25,32,48},
    {0,1,9,11,13,21,25,32},
    {0,1,5,16,17,21},
    {1,3,5,9,11,13,17,19,32,48},
    {0,1,5,7,9,16,17,25},
    {5,11,21,25,32,48},
    {0,5,9,17,25,48},
    {1,9,11,13,17,19,21,25,32,48},
    {0,1,13,48},
    {1,7,16,21,25,48},
    {1,5,9,13,17},
    {1,5,7,9,11,17,33},
    {1,3,9,11,17,33}]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem seedSpanWitness_parameters (i : Fin 19) :
    (∑ n ∈ seedSpanWitness i, seedEncodedParameters (seedOrbitParameterCode n))=
      binaryParameterGenerator (seedGeneratorIndex i) := by
  apply Prod.ext
  · funext p
    obtain ⟨r,rfl⟩ := rowEquiv.surjective p
    simp only [Prod.fst_sum,Finset.sum_apply]
    change (∑ n ∈ seedSpanWitness i, (seedEncodedParameters (seedOrbitParameterCode n)).1 (rowLabel r))=_
    decide +kernel +revert
  · apply Prod.ext
    · ext j k
      simp only [Prod.snd_sum,Prod.fst_sum,Matrix.sum_apply]
      fin_cases j <;> fin_cases k <;> decide +kernel +revert
    · ext j
      simp only [Prod.snd_sum,Finset.sum_apply]
      decide +kernel +revert

theorem seedOrbitEnumerate_surjective : Function.Surjective seedOrbitEnumerate := by
  decide +kernel

theorem seedOrbitResidue_mem (t : SeedOrbitIndex) : seedOrbitResidue t ∈ binaryResidue := by
  obtain ⟨n,rfl⟩ := seedOrbitEnumerate_surjective t
  rw [seedOrbitResidue_parameters]
  exact ⟨_,rfl⟩

theorem binaryGenerator_mem_seedSpan (i : Fin 19) :
    binaryNormalMap (binaryParameterGenerator (seedGeneratorIndex i)) ∈
      Submodule.span Bit (Set.range seedOrbitResidue) := by
  rw [← seedSpanWitness_parameters, map_sum]
  apply Submodule.sum_mem
  intro n hn
  rw [← seedOrbitResidue_parameters]
  exact Submodule.subset_span ⟨_,rfl⟩

theorem seedOrbitResidue_span :
    Submodule.span Bit (Set.range seedOrbitResidue)=binaryResidue := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨t,rfl⟩
    exact seedOrbitResidue_mem t
  · rintro w ⟨a,rfl⟩
    rw [binaryNormalMap_expansion]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    obtain ⟨j,rfl⟩ := seedGeneratorIndex_surjective i
    exact binaryGenerator_mem_seedSpan j


end Atlas.Rudvalis
