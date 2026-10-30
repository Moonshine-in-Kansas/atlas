import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseBasis
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseSimple
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseSimpleSecond
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeck
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckSecond
import Atlas.LinearGroups.Chevalley.Comparison.F4.SparseBasisCombination

/-! Literal integral identities. No finite-field or group-order certificate. -/
namespace Atlas.Chevalley.Comparison.F4
open scoped Matrix
open Atlas.LinearAlgebra.SparseIntegralMatrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem simple_square_0 :
    simpleMatrix 0 * simpleMatrix 0 = 2 • simpleSecondMatrix 0 := by
  simp only [← denote_simpleEntries 0, ← denote_simpleSecondEntries 0]
  simp only [← denote_product]
  decide +kernel

theorem simple_cube_0 :
    simpleSecondMatrix 0 * simpleMatrix 0 = 0 := by
  simp only [← denote_simpleEntries 0, ← denote_simpleSecondEntries 0]
  simp only [← denote_product]
  decide +kernel

theorem geck_square_0 :
    geckMatrix 0 * geckMatrix 0 = 2 • geckSecondMatrix 0 := by
  simp only [← denote_geckEntries 0, ← denote_geckSecondEntries 0]
  simp only [← denote_product]
  decide +kernel

theorem geck_cube_0 :
    geckSecondMatrix 0 * geckMatrix 0 = 0 := by
  simp only [← denote_geckEntries 0, ← denote_geckSecondEntries 0]
  simp only [← denote_product]
  decide +kernel

/-- Sparse propositions used only to isolate the individual kernel reductions.
They reference the existing lists; no matrix or coefficient table is copied. -/
private abbrev sparseCommutatorZero (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleEntries 0) (basisEntries j))
    (product (basisEntries j) (simpleEntries 0))) =
      denote (columnEntries basisEntries (geckEntries 0) j)

private abbrev sparseSecondConjugationZero (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleSecondEntries 0) (basisEntries j) ++
      product (basisEntries j) (simpleSecondEntries 0))
    (product (product (simpleEntries 0) (basisEntries j)) (simpleEntries 0))) =
      denote (columnEntries basisEntries (geckSecondEntries 0) j)

private theorem sparse_commutator_zero_0 : sparseCommutatorZero 0 := by
  decide +kernel

private theorem sparse_commutator_zero_1 : sparseCommutatorZero 1 := by
  decide +kernel

private theorem sparse_commutator_zero_2 : sparseCommutatorZero 2 := by
  decide +kernel

private theorem sparse_commutator_zero_3 : sparseCommutatorZero 3 := by
  decide +kernel

private theorem sparse_commutator_zero_4 : sparseCommutatorZero 4 := by
  decide +kernel

private theorem sparse_commutator_zero_5 : sparseCommutatorZero 5 := by
  decide +kernel

private theorem sparse_commutator_zero_6 : sparseCommutatorZero 6 := by
  decide +kernel

private theorem sparse_commutator_zero_7 : sparseCommutatorZero 7 := by
  decide +kernel

private theorem sparse_commutator_zero_8 : sparseCommutatorZero 8 := by
  decide +kernel

private theorem sparse_commutator_zero_9 : sparseCommutatorZero 9 := by
  decide +kernel

private theorem sparse_commutator_zero_10 : sparseCommutatorZero 10 := by
  decide +kernel

private theorem sparse_commutator_zero_11 : sparseCommutatorZero 11 := by
  decide +kernel

private theorem sparse_commutator_zero_12 : sparseCommutatorZero 12 := by
  decide +kernel

private theorem sparse_commutator_zero_13 : sparseCommutatorZero 13 := by
  decide +kernel

private theorem sparse_commutator_zero_14 : sparseCommutatorZero 14 := by
  decide +kernel

private theorem sparse_commutator_zero_15 : sparseCommutatorZero 15 := by
  decide +kernel

private theorem sparse_commutator_zero_16 : sparseCommutatorZero 16 := by
  decide +kernel

private theorem sparse_commutator_zero_17 : sparseCommutatorZero 17 := by
  decide +kernel

private theorem sparse_commutator_zero_18 : sparseCommutatorZero 18 := by
  decide +kernel

private theorem sparse_commutator_zero_19 : sparseCommutatorZero 19 := by
  decide +kernel

private theorem sparse_commutator_zero_20 : sparseCommutatorZero 20 := by
  decide +kernel

private theorem sparse_commutator_zero_21 : sparseCommutatorZero 21 := by
  decide +kernel

private theorem sparse_commutator_zero_22 : sparseCommutatorZero 22 := by
  decide +kernel

private theorem sparse_commutator_zero_23 : sparseCommutatorZero 23 := by
  decide +kernel

private theorem sparse_commutator_zero_24 : sparseCommutatorZero 24 := by
  decide +kernel

private theorem sparse_commutator_zero_25 : sparseCommutatorZero 25 := by
  decide +kernel

private theorem sparse_commutator_zero_26 : sparseCommutatorZero 26 := by
  decide +kernel

private theorem sparse_commutator_zero_27 : sparseCommutatorZero 27 := by
  decide +kernel

private theorem sparse_commutator_zero_28 : sparseCommutatorZero 28 := by
  decide +kernel

private theorem sparse_commutator_zero_29 : sparseCommutatorZero 29 := by
  decide +kernel

private theorem sparse_commutator_zero_30 : sparseCommutatorZero 30 := by
  decide +kernel

private theorem sparse_commutator_zero_31 : sparseCommutatorZero 31 := by
  decide +kernel

private theorem sparse_commutator_zero_32 : sparseCommutatorZero 32 := by
  decide +kernel

private theorem sparse_commutator_zero_33 : sparseCommutatorZero 33 := by
  decide +kernel

private theorem sparse_commutator_zero_34 : sparseCommutatorZero 34 := by
  decide +kernel

private theorem sparse_commutator_zero_35 : sparseCommutatorZero 35 := by
  decide +kernel

private theorem sparse_commutator_zero_36 : sparseCommutatorZero 36 := by
  decide +kernel

private theorem sparse_commutator_zero_37 : sparseCommutatorZero 37 := by
  decide +kernel

private theorem sparse_commutator_zero_38 : sparseCommutatorZero 38 := by
  decide +kernel

private theorem sparse_commutator_zero_39 : sparseCommutatorZero 39 := by
  decide +kernel

private theorem sparse_commutator_zero_40 : sparseCommutatorZero 40 := by
  decide +kernel

private theorem sparse_commutator_zero_41 : sparseCommutatorZero 41 := by
  decide +kernel

private theorem sparse_commutator_zero_42 : sparseCommutatorZero 42 := by
  decide +kernel

private theorem sparse_commutator_zero_43 : sparseCommutatorZero 43 := by
  decide +kernel

private theorem sparse_commutator_zero_44 : sparseCommutatorZero 44 := by
  decide +kernel

private theorem sparse_commutator_zero_45 : sparseCommutatorZero 45 := by
  decide +kernel

private theorem sparse_commutator_zero_46 : sparseCommutatorZero 46 := by
  decide +kernel

private theorem sparse_commutator_zero_47 : sparseCommutatorZero 47 := by
  decide +kernel

private theorem sparse_commutator_zero_48 : sparseCommutatorZero 48 := by
  decide +kernel

private theorem sparse_commutator_zero_49 : sparseCommutatorZero 49 := by
  decide +kernel

private theorem sparse_commutator_zero_50 : sparseCommutatorZero 50 := by
  decide +kernel

private theorem sparse_commutator_zero_51 : sparseCommutatorZero 51 := by
  decide +kernel

private theorem sparse_commutator_zero_all (j : Fin 52) : sparseCommutatorZero j := by
  fin_cases j
  · exact sparse_commutator_zero_0
  · exact sparse_commutator_zero_1
  · exact sparse_commutator_zero_2
  · exact sparse_commutator_zero_3
  · exact sparse_commutator_zero_4
  · exact sparse_commutator_zero_5
  · exact sparse_commutator_zero_6
  · exact sparse_commutator_zero_7
  · exact sparse_commutator_zero_8
  · exact sparse_commutator_zero_9
  · exact sparse_commutator_zero_10
  · exact sparse_commutator_zero_11
  · exact sparse_commutator_zero_12
  · exact sparse_commutator_zero_13
  · exact sparse_commutator_zero_14
  · exact sparse_commutator_zero_15
  · exact sparse_commutator_zero_16
  · exact sparse_commutator_zero_17
  · exact sparse_commutator_zero_18
  · exact sparse_commutator_zero_19
  · exact sparse_commutator_zero_20
  · exact sparse_commutator_zero_21
  · exact sparse_commutator_zero_22
  · exact sparse_commutator_zero_23
  · exact sparse_commutator_zero_24
  · exact sparse_commutator_zero_25
  · exact sparse_commutator_zero_26
  · exact sparse_commutator_zero_27
  · exact sparse_commutator_zero_28
  · exact sparse_commutator_zero_29
  · exact sparse_commutator_zero_30
  · exact sparse_commutator_zero_31
  · exact sparse_commutator_zero_32
  · exact sparse_commutator_zero_33
  · exact sparse_commutator_zero_34
  · exact sparse_commutator_zero_35
  · exact sparse_commutator_zero_36
  · exact sparse_commutator_zero_37
  · exact sparse_commutator_zero_38
  · exact sparse_commutator_zero_39
  · exact sparse_commutator_zero_40
  · exact sparse_commutator_zero_41
  · exact sparse_commutator_zero_42
  · exact sparse_commutator_zero_43
  · exact sparse_commutator_zero_44
  · exact sparse_commutator_zero_45
  · exact sparse_commutator_zero_46
  · exact sparse_commutator_zero_47
  · exact sparse_commutator_zero_48
  · exact sparse_commutator_zero_49
  · exact sparse_commutator_zero_50
  · exact sparse_commutator_zero_51

private theorem sparse_second_conjugation_zero_0 : sparseSecondConjugationZero 0 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_1 : sparseSecondConjugationZero 1 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_2 : sparseSecondConjugationZero 2 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_3 : sparseSecondConjugationZero 3 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_4 : sparseSecondConjugationZero 4 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_5 : sparseSecondConjugationZero 5 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_6 : sparseSecondConjugationZero 6 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_7 : sparseSecondConjugationZero 7 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_8 : sparseSecondConjugationZero 8 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_9 : sparseSecondConjugationZero 9 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_10 : sparseSecondConjugationZero 10 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_11 : sparseSecondConjugationZero 11 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_12 : sparseSecondConjugationZero 12 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_13 : sparseSecondConjugationZero 13 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_14 : sparseSecondConjugationZero 14 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_15 : sparseSecondConjugationZero 15 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_16 : sparseSecondConjugationZero 16 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_17 : sparseSecondConjugationZero 17 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_18 : sparseSecondConjugationZero 18 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_19 : sparseSecondConjugationZero 19 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_20 : sparseSecondConjugationZero 20 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_21 : sparseSecondConjugationZero 21 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_22 : sparseSecondConjugationZero 22 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_23 : sparseSecondConjugationZero 23 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_24 : sparseSecondConjugationZero 24 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_25 : sparseSecondConjugationZero 25 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_26 : sparseSecondConjugationZero 26 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_27 : sparseSecondConjugationZero 27 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_28 : sparseSecondConjugationZero 28 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_29 : sparseSecondConjugationZero 29 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_30 : sparseSecondConjugationZero 30 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_31 : sparseSecondConjugationZero 31 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_32 : sparseSecondConjugationZero 32 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_33 : sparseSecondConjugationZero 33 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_34 : sparseSecondConjugationZero 34 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_35 : sparseSecondConjugationZero 35 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_36 : sparseSecondConjugationZero 36 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_37 : sparseSecondConjugationZero 37 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_38 : sparseSecondConjugationZero 38 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_39 : sparseSecondConjugationZero 39 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_40 : sparseSecondConjugationZero 40 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_41 : sparseSecondConjugationZero 41 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_42 : sparseSecondConjugationZero 42 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_43 : sparseSecondConjugationZero 43 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_44 : sparseSecondConjugationZero 44 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_45 : sparseSecondConjugationZero 45 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_46 : sparseSecondConjugationZero 46 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_47 : sparseSecondConjugationZero 47 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_48 : sparseSecondConjugationZero 48 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_49 : sparseSecondConjugationZero 49 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_50 : sparseSecondConjugationZero 50 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_51 : sparseSecondConjugationZero 51 := by
  decide +kernel

private theorem sparse_second_conjugation_zero_all (j : Fin 52) : sparseSecondConjugationZero j := by
  fin_cases j
  · exact sparse_second_conjugation_zero_0
  · exact sparse_second_conjugation_zero_1
  · exact sparse_second_conjugation_zero_2
  · exact sparse_second_conjugation_zero_3
  · exact sparse_second_conjugation_zero_4
  · exact sparse_second_conjugation_zero_5
  · exact sparse_second_conjugation_zero_6
  · exact sparse_second_conjugation_zero_7
  · exact sparse_second_conjugation_zero_8
  · exact sparse_second_conjugation_zero_9
  · exact sparse_second_conjugation_zero_10
  · exact sparse_second_conjugation_zero_11
  · exact sparse_second_conjugation_zero_12
  · exact sparse_second_conjugation_zero_13
  · exact sparse_second_conjugation_zero_14
  · exact sparse_second_conjugation_zero_15
  · exact sparse_second_conjugation_zero_16
  · exact sparse_second_conjugation_zero_17
  · exact sparse_second_conjugation_zero_18
  · exact sparse_second_conjugation_zero_19
  · exact sparse_second_conjugation_zero_20
  · exact sparse_second_conjugation_zero_21
  · exact sparse_second_conjugation_zero_22
  · exact sparse_second_conjugation_zero_23
  · exact sparse_second_conjugation_zero_24
  · exact sparse_second_conjugation_zero_25
  · exact sparse_second_conjugation_zero_26
  · exact sparse_second_conjugation_zero_27
  · exact sparse_second_conjugation_zero_28
  · exact sparse_second_conjugation_zero_29
  · exact sparse_second_conjugation_zero_30
  · exact sparse_second_conjugation_zero_31
  · exact sparse_second_conjugation_zero_32
  · exact sparse_second_conjugation_zero_33
  · exact sparse_second_conjugation_zero_34
  · exact sparse_second_conjugation_zero_35
  · exact sparse_second_conjugation_zero_36
  · exact sparse_second_conjugation_zero_37
  · exact sparse_second_conjugation_zero_38
  · exact sparse_second_conjugation_zero_39
  · exact sparse_second_conjugation_zero_40
  · exact sparse_second_conjugation_zero_41
  · exact sparse_second_conjugation_zero_42
  · exact sparse_second_conjugation_zero_43
  · exact sparse_second_conjugation_zero_44
  · exact sparse_second_conjugation_zero_45
  · exact sparse_second_conjugation_zero_46
  · exact sparse_second_conjugation_zero_47
  · exact sparse_second_conjugation_zero_48
  · exact sparse_second_conjugation_zero_49
  · exact sparse_second_conjugation_zero_50
  · exact sparse_second_conjugation_zero_51

theorem simple_commutator_0 : ∀ j : Fin 52,
    simpleMatrix 0 * basisMatrix j - basisMatrix j * simpleMatrix 0 =
      basisCombination (fun k => geckMatrix 0 k j) := by
  intro j
  rw [← denote_geckEntries 0, basisCombination_denote_column]
  simp only [← denote_simpleEntries 0, ← denote_basisEntries j,
    ← denote_product, ← denote_subEntries]
  exact sparse_commutator_zero_all j

theorem simple_second_conjugation_0 : ∀ j : Fin 52,
    simpleSecondMatrix 0 * basisMatrix j + basisMatrix j * simpleSecondMatrix 0 -
      simpleMatrix 0 * basisMatrix j * simpleMatrix 0 =
        basisCombination (fun k => geckSecondMatrix 0 k j) := by
  intro j
  rw [← denote_geckSecondEntries 0, basisCombination_denote_column]
  simp only [← denote_simpleEntries 0, ← denote_simpleSecondEntries 0,
    ← denote_basisEntries j, ← denote_product, ← denote_append,
    ← denote_subEntries]
  exact sparse_second_conjugation_zero_all j

theorem simple_third_conjugation_0 : ∀ j : Fin 52,
    simpleMatrix 0 * basisMatrix j * simpleSecondMatrix 0 -
      simpleSecondMatrix 0 * basisMatrix j * simpleMatrix 0 = 0 := by
  intro j
  simp only [← denote_simpleEntries 0, ← denote_simpleSecondEntries 0, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

theorem simple_fourth_conjugation_0 : ∀ j : Fin 52,
    simpleSecondMatrix 0 * basisMatrix j * simpleSecondMatrix 0 = 0 := by
  intro j
  simp only [← denote_simpleSecondEntries 0, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

end Atlas.Chevalley.Comparison.F4
