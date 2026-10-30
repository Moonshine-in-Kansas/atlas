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

theorem simple_square_1 :
    simpleMatrix 1 * simpleMatrix 1 = 2 • simpleSecondMatrix 1 := by
  simp only [← denote_simpleEntries 1, ← denote_simpleSecondEntries 1]
  simp only [← denote_product]
  decide +kernel

theorem simple_cube_1 :
    simpleSecondMatrix 1 * simpleMatrix 1 = 0 := by
  simp only [← denote_simpleEntries 1, ← denote_simpleSecondEntries 1]
  simp only [← denote_product]
  decide +kernel

theorem geck_square_1 :
    geckMatrix 1 * geckMatrix 1 = 2 • geckSecondMatrix 1 := by
  simp only [← denote_geckEntries 1, ← denote_geckSecondEntries 1]
  simp only [← denote_product]
  decide +kernel

theorem geck_cube_1 :
    geckSecondMatrix 1 * geckMatrix 1 = 0 := by
  simp only [← denote_geckEntries 1, ← denote_geckSecondEntries 1]
  simp only [← denote_product]
  decide +kernel

/-- Sparse propositions isolate individual column reductions. They use the
existing lists and introduce no new matrix or coefficient table. -/
private abbrev sparseCommutatorRoot1 (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleEntries 1) (basisEntries j))
    (product (basisEntries j) (simpleEntries 1))) =
      denote (columnEntries basisEntries (geckEntries 1) j)

private abbrev sparseSecondConjugationRoot1 (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleSecondEntries 1) (basisEntries j) ++
      product (basisEntries j) (simpleSecondEntries 1))
    (product (product (simpleEntries 1) (basisEntries j)) (simpleEntries 1))) =
      denote (columnEntries basisEntries (geckSecondEntries 1) j)

private theorem sparse_commutator_root1_column0 : sparseCommutatorRoot1 0 := by
  decide +kernel

private theorem sparse_commutator_root1_column1 : sparseCommutatorRoot1 1 := by
  decide +kernel

private theorem sparse_commutator_root1_column2 : sparseCommutatorRoot1 2 := by
  decide +kernel

private theorem sparse_commutator_root1_column3 : sparseCommutatorRoot1 3 := by
  decide +kernel

private theorem sparse_commutator_root1_column4 : sparseCommutatorRoot1 4 := by
  decide +kernel

private theorem sparse_commutator_root1_column5 : sparseCommutatorRoot1 5 := by
  decide +kernel

private theorem sparse_commutator_root1_column6 : sparseCommutatorRoot1 6 := by
  decide +kernel

private theorem sparse_commutator_root1_column7 : sparseCommutatorRoot1 7 := by
  decide +kernel

private theorem sparse_commutator_root1_column8 : sparseCommutatorRoot1 8 := by
  decide +kernel

private theorem sparse_commutator_root1_column9 : sparseCommutatorRoot1 9 := by
  decide +kernel

private theorem sparse_commutator_root1_column10 : sparseCommutatorRoot1 10 := by
  decide +kernel

private theorem sparse_commutator_root1_column11 : sparseCommutatorRoot1 11 := by
  decide +kernel

private theorem sparse_commutator_root1_column12 : sparseCommutatorRoot1 12 := by
  decide +kernel

private theorem sparse_commutator_root1_column13 : sparseCommutatorRoot1 13 := by
  decide +kernel

private theorem sparse_commutator_root1_column14 : sparseCommutatorRoot1 14 := by
  decide +kernel

private theorem sparse_commutator_root1_column15 : sparseCommutatorRoot1 15 := by
  decide +kernel

private theorem sparse_commutator_root1_column16 : sparseCommutatorRoot1 16 := by
  decide +kernel

private theorem sparse_commutator_root1_column17 : sparseCommutatorRoot1 17 := by
  decide +kernel

private theorem sparse_commutator_root1_column18 : sparseCommutatorRoot1 18 := by
  decide +kernel

private theorem sparse_commutator_root1_column19 : sparseCommutatorRoot1 19 := by
  decide +kernel

private theorem sparse_commutator_root1_column20 : sparseCommutatorRoot1 20 := by
  decide +kernel

private theorem sparse_commutator_root1_column21 : sparseCommutatorRoot1 21 := by
  decide +kernel

private theorem sparse_commutator_root1_column22 : sparseCommutatorRoot1 22 := by
  decide +kernel

private theorem sparse_commutator_root1_column23 : sparseCommutatorRoot1 23 := by
  decide +kernel

private theorem sparse_commutator_root1_column24 : sparseCommutatorRoot1 24 := by
  decide +kernel

private theorem sparse_commutator_root1_column25 : sparseCommutatorRoot1 25 := by
  decide +kernel

private theorem sparse_commutator_root1_column26 : sparseCommutatorRoot1 26 := by
  decide +kernel

private theorem sparse_commutator_root1_column27 : sparseCommutatorRoot1 27 := by
  decide +kernel

private theorem sparse_commutator_root1_column28 : sparseCommutatorRoot1 28 := by
  decide +kernel

private theorem sparse_commutator_root1_column29 : sparseCommutatorRoot1 29 := by
  decide +kernel

private theorem sparse_commutator_root1_column30 : sparseCommutatorRoot1 30 := by
  decide +kernel

private theorem sparse_commutator_root1_column31 : sparseCommutatorRoot1 31 := by
  decide +kernel

private theorem sparse_commutator_root1_column32 : sparseCommutatorRoot1 32 := by
  decide +kernel

private theorem sparse_commutator_root1_column33 : sparseCommutatorRoot1 33 := by
  decide +kernel

private theorem sparse_commutator_root1_column34 : sparseCommutatorRoot1 34 := by
  decide +kernel

private theorem sparse_commutator_root1_column35 : sparseCommutatorRoot1 35 := by
  decide +kernel

private theorem sparse_commutator_root1_column36 : sparseCommutatorRoot1 36 := by
  decide +kernel

private theorem sparse_commutator_root1_column37 : sparseCommutatorRoot1 37 := by
  decide +kernel

private theorem sparse_commutator_root1_column38 : sparseCommutatorRoot1 38 := by
  decide +kernel

private theorem sparse_commutator_root1_column39 : sparseCommutatorRoot1 39 := by
  decide +kernel

private theorem sparse_commutator_root1_column40 : sparseCommutatorRoot1 40 := by
  decide +kernel

private theorem sparse_commutator_root1_column41 : sparseCommutatorRoot1 41 := by
  decide +kernel

private theorem sparse_commutator_root1_column42 : sparseCommutatorRoot1 42 := by
  decide +kernel

private theorem sparse_commutator_root1_column43 : sparseCommutatorRoot1 43 := by
  decide +kernel

private theorem sparse_commutator_root1_column44 : sparseCommutatorRoot1 44 := by
  decide +kernel

private theorem sparse_commutator_root1_column45 : sparseCommutatorRoot1 45 := by
  decide +kernel

private theorem sparse_commutator_root1_column46 : sparseCommutatorRoot1 46 := by
  decide +kernel

private theorem sparse_commutator_root1_column47 : sparseCommutatorRoot1 47 := by
  decide +kernel

private theorem sparse_commutator_root1_column48 : sparseCommutatorRoot1 48 := by
  decide +kernel

private theorem sparse_commutator_root1_column49 : sparseCommutatorRoot1 49 := by
  decide +kernel

private theorem sparse_commutator_root1_column50 : sparseCommutatorRoot1 50 := by
  decide +kernel

private theorem sparse_commutator_root1_column51 : sparseCommutatorRoot1 51 := by
  decide +kernel

private theorem sparse_commutator_root1_all (j : Fin 52) : sparseCommutatorRoot1 j := by
  fin_cases j
  · exact sparse_commutator_root1_column0
  · exact sparse_commutator_root1_column1
  · exact sparse_commutator_root1_column2
  · exact sparse_commutator_root1_column3
  · exact sparse_commutator_root1_column4
  · exact sparse_commutator_root1_column5
  · exact sparse_commutator_root1_column6
  · exact sparse_commutator_root1_column7
  · exact sparse_commutator_root1_column8
  · exact sparse_commutator_root1_column9
  · exact sparse_commutator_root1_column10
  · exact sparse_commutator_root1_column11
  · exact sparse_commutator_root1_column12
  · exact sparse_commutator_root1_column13
  · exact sparse_commutator_root1_column14
  · exact sparse_commutator_root1_column15
  · exact sparse_commutator_root1_column16
  · exact sparse_commutator_root1_column17
  · exact sparse_commutator_root1_column18
  · exact sparse_commutator_root1_column19
  · exact sparse_commutator_root1_column20
  · exact sparse_commutator_root1_column21
  · exact sparse_commutator_root1_column22
  · exact sparse_commutator_root1_column23
  · exact sparse_commutator_root1_column24
  · exact sparse_commutator_root1_column25
  · exact sparse_commutator_root1_column26
  · exact sparse_commutator_root1_column27
  · exact sparse_commutator_root1_column28
  · exact sparse_commutator_root1_column29
  · exact sparse_commutator_root1_column30
  · exact sparse_commutator_root1_column31
  · exact sparse_commutator_root1_column32
  · exact sparse_commutator_root1_column33
  · exact sparse_commutator_root1_column34
  · exact sparse_commutator_root1_column35
  · exact sparse_commutator_root1_column36
  · exact sparse_commutator_root1_column37
  · exact sparse_commutator_root1_column38
  · exact sparse_commutator_root1_column39
  · exact sparse_commutator_root1_column40
  · exact sparse_commutator_root1_column41
  · exact sparse_commutator_root1_column42
  · exact sparse_commutator_root1_column43
  · exact sparse_commutator_root1_column44
  · exact sparse_commutator_root1_column45
  · exact sparse_commutator_root1_column46
  · exact sparse_commutator_root1_column47
  · exact sparse_commutator_root1_column48
  · exact sparse_commutator_root1_column49
  · exact sparse_commutator_root1_column50
  · exact sparse_commutator_root1_column51

private theorem sparse_second_conjugation_root1_column0 : sparseSecondConjugationRoot1 0 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column1 : sparseSecondConjugationRoot1 1 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column2 : sparseSecondConjugationRoot1 2 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column3 : sparseSecondConjugationRoot1 3 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column4 : sparseSecondConjugationRoot1 4 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column5 : sparseSecondConjugationRoot1 5 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column6 : sparseSecondConjugationRoot1 6 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column7 : sparseSecondConjugationRoot1 7 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column8 : sparseSecondConjugationRoot1 8 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column9 : sparseSecondConjugationRoot1 9 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column10 : sparseSecondConjugationRoot1 10 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column11 : sparseSecondConjugationRoot1 11 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column12 : sparseSecondConjugationRoot1 12 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column13 : sparseSecondConjugationRoot1 13 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column14 : sparseSecondConjugationRoot1 14 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column15 : sparseSecondConjugationRoot1 15 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column16 : sparseSecondConjugationRoot1 16 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column17 : sparseSecondConjugationRoot1 17 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column18 : sparseSecondConjugationRoot1 18 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column19 : sparseSecondConjugationRoot1 19 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column20 : sparseSecondConjugationRoot1 20 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column21 : sparseSecondConjugationRoot1 21 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column22 : sparseSecondConjugationRoot1 22 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column23 : sparseSecondConjugationRoot1 23 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column24 : sparseSecondConjugationRoot1 24 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column25 : sparseSecondConjugationRoot1 25 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column26 : sparseSecondConjugationRoot1 26 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column27 : sparseSecondConjugationRoot1 27 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column28 : sparseSecondConjugationRoot1 28 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column29 : sparseSecondConjugationRoot1 29 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column30 : sparseSecondConjugationRoot1 30 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column31 : sparseSecondConjugationRoot1 31 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column32 : sparseSecondConjugationRoot1 32 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column33 : sparseSecondConjugationRoot1 33 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column34 : sparseSecondConjugationRoot1 34 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column35 : sparseSecondConjugationRoot1 35 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column36 : sparseSecondConjugationRoot1 36 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column37 : sparseSecondConjugationRoot1 37 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column38 : sparseSecondConjugationRoot1 38 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column39 : sparseSecondConjugationRoot1 39 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column40 : sparseSecondConjugationRoot1 40 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column41 : sparseSecondConjugationRoot1 41 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column42 : sparseSecondConjugationRoot1 42 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column43 : sparseSecondConjugationRoot1 43 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column44 : sparseSecondConjugationRoot1 44 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column45 : sparseSecondConjugationRoot1 45 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column46 : sparseSecondConjugationRoot1 46 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column47 : sparseSecondConjugationRoot1 47 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column48 : sparseSecondConjugationRoot1 48 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column49 : sparseSecondConjugationRoot1 49 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column50 : sparseSecondConjugationRoot1 50 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_column51 : sparseSecondConjugationRoot1 51 := by
  decide +kernel

private theorem sparse_second_conjugation_root1_all (j : Fin 52) : sparseSecondConjugationRoot1 j := by
  fin_cases j
  · exact sparse_second_conjugation_root1_column0
  · exact sparse_second_conjugation_root1_column1
  · exact sparse_second_conjugation_root1_column2
  · exact sparse_second_conjugation_root1_column3
  · exact sparse_second_conjugation_root1_column4
  · exact sparse_second_conjugation_root1_column5
  · exact sparse_second_conjugation_root1_column6
  · exact sparse_second_conjugation_root1_column7
  · exact sparse_second_conjugation_root1_column8
  · exact sparse_second_conjugation_root1_column9
  · exact sparse_second_conjugation_root1_column10
  · exact sparse_second_conjugation_root1_column11
  · exact sparse_second_conjugation_root1_column12
  · exact sparse_second_conjugation_root1_column13
  · exact sparse_second_conjugation_root1_column14
  · exact sparse_second_conjugation_root1_column15
  · exact sparse_second_conjugation_root1_column16
  · exact sparse_second_conjugation_root1_column17
  · exact sparse_second_conjugation_root1_column18
  · exact sparse_second_conjugation_root1_column19
  · exact sparse_second_conjugation_root1_column20
  · exact sparse_second_conjugation_root1_column21
  · exact sparse_second_conjugation_root1_column22
  · exact sparse_second_conjugation_root1_column23
  · exact sparse_second_conjugation_root1_column24
  · exact sparse_second_conjugation_root1_column25
  · exact sparse_second_conjugation_root1_column26
  · exact sparse_second_conjugation_root1_column27
  · exact sparse_second_conjugation_root1_column28
  · exact sparse_second_conjugation_root1_column29
  · exact sparse_second_conjugation_root1_column30
  · exact sparse_second_conjugation_root1_column31
  · exact sparse_second_conjugation_root1_column32
  · exact sparse_second_conjugation_root1_column33
  · exact sparse_second_conjugation_root1_column34
  · exact sparse_second_conjugation_root1_column35
  · exact sparse_second_conjugation_root1_column36
  · exact sparse_second_conjugation_root1_column37
  · exact sparse_second_conjugation_root1_column38
  · exact sparse_second_conjugation_root1_column39
  · exact sparse_second_conjugation_root1_column40
  · exact sparse_second_conjugation_root1_column41
  · exact sparse_second_conjugation_root1_column42
  · exact sparse_second_conjugation_root1_column43
  · exact sparse_second_conjugation_root1_column44
  · exact sparse_second_conjugation_root1_column45
  · exact sparse_second_conjugation_root1_column46
  · exact sparse_second_conjugation_root1_column47
  · exact sparse_second_conjugation_root1_column48
  · exact sparse_second_conjugation_root1_column49
  · exact sparse_second_conjugation_root1_column50
  · exact sparse_second_conjugation_root1_column51

theorem simple_commutator_1 : ∀ j : Fin 52,
    simpleMatrix 1 * basisMatrix j - basisMatrix j * simpleMatrix 1 =
      basisCombination (fun k => geckMatrix 1 k j) := by
  intro j
  rw [← denote_geckEntries 1, basisCombination_denote_column]
  simp only [← denote_simpleEntries 1, ← denote_basisEntries j,
    ← denote_product, ← denote_subEntries]
  exact sparse_commutator_root1_all j

theorem simple_second_conjugation_1 : ∀ j : Fin 52,
    simpleSecondMatrix 1 * basisMatrix j + basisMatrix j * simpleSecondMatrix 1 -
      simpleMatrix 1 * basisMatrix j * simpleMatrix 1 =
        basisCombination (fun k => geckSecondMatrix 1 k j) := by
  intro j
  rw [← denote_geckSecondEntries 1, basisCombination_denote_column]
  simp only [← denote_simpleEntries 1, ← denote_simpleSecondEntries 1,
    ← denote_basisEntries j, ← denote_product, ← denote_append,
    ← denote_subEntries]
  exact sparse_second_conjugation_root1_all j

theorem simple_third_conjugation_1 : ∀ j : Fin 52,
    simpleMatrix 1 * basisMatrix j * simpleSecondMatrix 1 -
      simpleSecondMatrix 1 * basisMatrix j * simpleMatrix 1 = 0 := by
  intro j
  simp only [← denote_simpleEntries 1, ← denote_simpleSecondEntries 1, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

theorem simple_fourth_conjugation_1 : ∀ j : Fin 52,
    simpleSecondMatrix 1 * basisMatrix j * simpleSecondMatrix 1 = 0 := by
  intro j
  simp only [← denote_simpleSecondEntries 1, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

end Atlas.Chevalley.Comparison.F4
