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

theorem simple_square_4 :
    simpleMatrix 4 * simpleMatrix 4 = 2 • simpleSecondMatrix 4 := by
  simp only [← denote_simpleEntries 4, ← denote_simpleSecondEntries 4]
  simp only [← denote_product]
  decide +kernel

theorem simple_cube_4 :
    simpleSecondMatrix 4 * simpleMatrix 4 = 0 := by
  simp only [← denote_simpleEntries 4, ← denote_simpleSecondEntries 4]
  simp only [← denote_product]
  decide +kernel

theorem geck_square_4 :
    geckMatrix 4 * geckMatrix 4 = 2 • geckSecondMatrix 4 := by
  simp only [← denote_geckEntries 4, ← denote_geckSecondEntries 4]
  simp only [← denote_product]
  decide +kernel

theorem geck_cube_4 :
    geckSecondMatrix 4 * geckMatrix 4 = 0 := by
  simp only [← denote_geckEntries 4, ← denote_geckSecondEntries 4]
  simp only [← denote_product]
  decide +kernel

/-- Sparse propositions isolate individual column reductions. They use the
existing lists and introduce no new matrix or coefficient table. -/
private abbrev sparseCommutatorRoot4 (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleEntries 4) (basisEntries j))
    (product (basisEntries j) (simpleEntries 4))) =
      denote (columnEntries basisEntries (geckEntries 4) j)

private abbrev sparseSecondConjugationRoot4 (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleSecondEntries 4) (basisEntries j) ++
      product (basisEntries j) (simpleSecondEntries 4))
    (product (product (simpleEntries 4) (basisEntries j)) (simpleEntries 4))) =
      denote (columnEntries basisEntries (geckSecondEntries 4) j)

private theorem sparse_commutator_root4_column0 : sparseCommutatorRoot4 0 := by
  decide +kernel

private theorem sparse_commutator_root4_column1 : sparseCommutatorRoot4 1 := by
  decide +kernel

private theorem sparse_commutator_root4_column2 : sparseCommutatorRoot4 2 := by
  decide +kernel

private theorem sparse_commutator_root4_column3 : sparseCommutatorRoot4 3 := by
  decide +kernel

private theorem sparse_commutator_root4_column4 : sparseCommutatorRoot4 4 := by
  decide +kernel

private theorem sparse_commutator_root4_column5 : sparseCommutatorRoot4 5 := by
  decide +kernel

private theorem sparse_commutator_root4_column6 : sparseCommutatorRoot4 6 := by
  decide +kernel

private theorem sparse_commutator_root4_column7 : sparseCommutatorRoot4 7 := by
  decide +kernel

private theorem sparse_commutator_root4_column8 : sparseCommutatorRoot4 8 := by
  decide +kernel

private theorem sparse_commutator_root4_column9 : sparseCommutatorRoot4 9 := by
  decide +kernel

private theorem sparse_commutator_root4_column10 : sparseCommutatorRoot4 10 := by
  decide +kernel

private theorem sparse_commutator_root4_column11 : sparseCommutatorRoot4 11 := by
  decide +kernel

private theorem sparse_commutator_root4_column12 : sparseCommutatorRoot4 12 := by
  decide +kernel

private theorem sparse_commutator_root4_column13 : sparseCommutatorRoot4 13 := by
  decide +kernel

private theorem sparse_commutator_root4_column14 : sparseCommutatorRoot4 14 := by
  decide +kernel

private theorem sparse_commutator_root4_column15 : sparseCommutatorRoot4 15 := by
  decide +kernel

private theorem sparse_commutator_root4_column16 : sparseCommutatorRoot4 16 := by
  decide +kernel

private theorem sparse_commutator_root4_column17 : sparseCommutatorRoot4 17 := by
  decide +kernel

private theorem sparse_commutator_root4_column18 : sparseCommutatorRoot4 18 := by
  decide +kernel

private theorem sparse_commutator_root4_column19 : sparseCommutatorRoot4 19 := by
  decide +kernel

private theorem sparse_commutator_root4_column20 : sparseCommutatorRoot4 20 := by
  decide +kernel

private theorem sparse_commutator_root4_column21 : sparseCommutatorRoot4 21 := by
  decide +kernel

private theorem sparse_commutator_root4_column22 : sparseCommutatorRoot4 22 := by
  decide +kernel

private theorem sparse_commutator_root4_column23 : sparseCommutatorRoot4 23 := by
  decide +kernel

private theorem sparse_commutator_root4_column24 : sparseCommutatorRoot4 24 := by
  decide +kernel

private theorem sparse_commutator_root4_column25 : sparseCommutatorRoot4 25 := by
  decide +kernel

private theorem sparse_commutator_root4_column26 : sparseCommutatorRoot4 26 := by
  decide +kernel

private theorem sparse_commutator_root4_column27 : sparseCommutatorRoot4 27 := by
  decide +kernel

private theorem sparse_commutator_root4_column28 : sparseCommutatorRoot4 28 := by
  decide +kernel

private theorem sparse_commutator_root4_column29 : sparseCommutatorRoot4 29 := by
  decide +kernel

private theorem sparse_commutator_root4_column30 : sparseCommutatorRoot4 30 := by
  decide +kernel

private theorem sparse_commutator_root4_column31 : sparseCommutatorRoot4 31 := by
  decide +kernel

private theorem sparse_commutator_root4_column32 : sparseCommutatorRoot4 32 := by
  decide +kernel

private theorem sparse_commutator_root4_column33 : sparseCommutatorRoot4 33 := by
  decide +kernel

private theorem sparse_commutator_root4_column34 : sparseCommutatorRoot4 34 := by
  decide +kernel

private theorem sparse_commutator_root4_column35 : sparseCommutatorRoot4 35 := by
  decide +kernel

private theorem sparse_commutator_root4_column36 : sparseCommutatorRoot4 36 := by
  decide +kernel

private theorem sparse_commutator_root4_column37 : sparseCommutatorRoot4 37 := by
  decide +kernel

private theorem sparse_commutator_root4_column38 : sparseCommutatorRoot4 38 := by
  decide +kernel

private theorem sparse_commutator_root4_column39 : sparseCommutatorRoot4 39 := by
  decide +kernel

private theorem sparse_commutator_root4_column40 : sparseCommutatorRoot4 40 := by
  decide +kernel

private theorem sparse_commutator_root4_column41 : sparseCommutatorRoot4 41 := by
  decide +kernel

private theorem sparse_commutator_root4_column42 : sparseCommutatorRoot4 42 := by
  decide +kernel

private theorem sparse_commutator_root4_column43 : sparseCommutatorRoot4 43 := by
  decide +kernel

private theorem sparse_commutator_root4_column44 : sparseCommutatorRoot4 44 := by
  decide +kernel

private theorem sparse_commutator_root4_column45 : sparseCommutatorRoot4 45 := by
  decide +kernel

private theorem sparse_commutator_root4_column46 : sparseCommutatorRoot4 46 := by
  decide +kernel

private theorem sparse_commutator_root4_column47 : sparseCommutatorRoot4 47 := by
  decide +kernel

private theorem sparse_commutator_root4_column48 : sparseCommutatorRoot4 48 := by
  decide +kernel

private theorem sparse_commutator_root4_column49 : sparseCommutatorRoot4 49 := by
  decide +kernel

private theorem sparse_commutator_root4_column50 : sparseCommutatorRoot4 50 := by
  decide +kernel

private theorem sparse_commutator_root4_column51 : sparseCommutatorRoot4 51 := by
  decide +kernel

private theorem sparse_commutator_root4_all (j : Fin 52) : sparseCommutatorRoot4 j := by
  fin_cases j
  · exact sparse_commutator_root4_column0
  · exact sparse_commutator_root4_column1
  · exact sparse_commutator_root4_column2
  · exact sparse_commutator_root4_column3
  · exact sparse_commutator_root4_column4
  · exact sparse_commutator_root4_column5
  · exact sparse_commutator_root4_column6
  · exact sparse_commutator_root4_column7
  · exact sparse_commutator_root4_column8
  · exact sparse_commutator_root4_column9
  · exact sparse_commutator_root4_column10
  · exact sparse_commutator_root4_column11
  · exact sparse_commutator_root4_column12
  · exact sparse_commutator_root4_column13
  · exact sparse_commutator_root4_column14
  · exact sparse_commutator_root4_column15
  · exact sparse_commutator_root4_column16
  · exact sparse_commutator_root4_column17
  · exact sparse_commutator_root4_column18
  · exact sparse_commutator_root4_column19
  · exact sparse_commutator_root4_column20
  · exact sparse_commutator_root4_column21
  · exact sparse_commutator_root4_column22
  · exact sparse_commutator_root4_column23
  · exact sparse_commutator_root4_column24
  · exact sparse_commutator_root4_column25
  · exact sparse_commutator_root4_column26
  · exact sparse_commutator_root4_column27
  · exact sparse_commutator_root4_column28
  · exact sparse_commutator_root4_column29
  · exact sparse_commutator_root4_column30
  · exact sparse_commutator_root4_column31
  · exact sparse_commutator_root4_column32
  · exact sparse_commutator_root4_column33
  · exact sparse_commutator_root4_column34
  · exact sparse_commutator_root4_column35
  · exact sparse_commutator_root4_column36
  · exact sparse_commutator_root4_column37
  · exact sparse_commutator_root4_column38
  · exact sparse_commutator_root4_column39
  · exact sparse_commutator_root4_column40
  · exact sparse_commutator_root4_column41
  · exact sparse_commutator_root4_column42
  · exact sparse_commutator_root4_column43
  · exact sparse_commutator_root4_column44
  · exact sparse_commutator_root4_column45
  · exact sparse_commutator_root4_column46
  · exact sparse_commutator_root4_column47
  · exact sparse_commutator_root4_column48
  · exact sparse_commutator_root4_column49
  · exact sparse_commutator_root4_column50
  · exact sparse_commutator_root4_column51

private theorem sparse_second_conjugation_root4_column0 : sparseSecondConjugationRoot4 0 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column1 : sparseSecondConjugationRoot4 1 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column2 : sparseSecondConjugationRoot4 2 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column3 : sparseSecondConjugationRoot4 3 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column4 : sparseSecondConjugationRoot4 4 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column5 : sparseSecondConjugationRoot4 5 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column6 : sparseSecondConjugationRoot4 6 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column7 : sparseSecondConjugationRoot4 7 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column8 : sparseSecondConjugationRoot4 8 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column9 : sparseSecondConjugationRoot4 9 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column10 : sparseSecondConjugationRoot4 10 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column11 : sparseSecondConjugationRoot4 11 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column12 : sparseSecondConjugationRoot4 12 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column13 : sparseSecondConjugationRoot4 13 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column14 : sparseSecondConjugationRoot4 14 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column15 : sparseSecondConjugationRoot4 15 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column16 : sparseSecondConjugationRoot4 16 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column17 : sparseSecondConjugationRoot4 17 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column18 : sparseSecondConjugationRoot4 18 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column19 : sparseSecondConjugationRoot4 19 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column20 : sparseSecondConjugationRoot4 20 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column21 : sparseSecondConjugationRoot4 21 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column22 : sparseSecondConjugationRoot4 22 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column23 : sparseSecondConjugationRoot4 23 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column24 : sparseSecondConjugationRoot4 24 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column25 : sparseSecondConjugationRoot4 25 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column26 : sparseSecondConjugationRoot4 26 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column27 : sparseSecondConjugationRoot4 27 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column28 : sparseSecondConjugationRoot4 28 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column29 : sparseSecondConjugationRoot4 29 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column30 : sparseSecondConjugationRoot4 30 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column31 : sparseSecondConjugationRoot4 31 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column32 : sparseSecondConjugationRoot4 32 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column33 : sparseSecondConjugationRoot4 33 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column34 : sparseSecondConjugationRoot4 34 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column35 : sparseSecondConjugationRoot4 35 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column36 : sparseSecondConjugationRoot4 36 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column37 : sparseSecondConjugationRoot4 37 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column38 : sparseSecondConjugationRoot4 38 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column39 : sparseSecondConjugationRoot4 39 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column40 : sparseSecondConjugationRoot4 40 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column41 : sparseSecondConjugationRoot4 41 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column42 : sparseSecondConjugationRoot4 42 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column43 : sparseSecondConjugationRoot4 43 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column44 : sparseSecondConjugationRoot4 44 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column45 : sparseSecondConjugationRoot4 45 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column46 : sparseSecondConjugationRoot4 46 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column47 : sparseSecondConjugationRoot4 47 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column48 : sparseSecondConjugationRoot4 48 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column49 : sparseSecondConjugationRoot4 49 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column50 : sparseSecondConjugationRoot4 50 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_column51 : sparseSecondConjugationRoot4 51 := by
  decide +kernel

private theorem sparse_second_conjugation_root4_all (j : Fin 52) : sparseSecondConjugationRoot4 j := by
  fin_cases j
  · exact sparse_second_conjugation_root4_column0
  · exact sparse_second_conjugation_root4_column1
  · exact sparse_second_conjugation_root4_column2
  · exact sparse_second_conjugation_root4_column3
  · exact sparse_second_conjugation_root4_column4
  · exact sparse_second_conjugation_root4_column5
  · exact sparse_second_conjugation_root4_column6
  · exact sparse_second_conjugation_root4_column7
  · exact sparse_second_conjugation_root4_column8
  · exact sparse_second_conjugation_root4_column9
  · exact sparse_second_conjugation_root4_column10
  · exact sparse_second_conjugation_root4_column11
  · exact sparse_second_conjugation_root4_column12
  · exact sparse_second_conjugation_root4_column13
  · exact sparse_second_conjugation_root4_column14
  · exact sparse_second_conjugation_root4_column15
  · exact sparse_second_conjugation_root4_column16
  · exact sparse_second_conjugation_root4_column17
  · exact sparse_second_conjugation_root4_column18
  · exact sparse_second_conjugation_root4_column19
  · exact sparse_second_conjugation_root4_column20
  · exact sparse_second_conjugation_root4_column21
  · exact sparse_second_conjugation_root4_column22
  · exact sparse_second_conjugation_root4_column23
  · exact sparse_second_conjugation_root4_column24
  · exact sparse_second_conjugation_root4_column25
  · exact sparse_second_conjugation_root4_column26
  · exact sparse_second_conjugation_root4_column27
  · exact sparse_second_conjugation_root4_column28
  · exact sparse_second_conjugation_root4_column29
  · exact sparse_second_conjugation_root4_column30
  · exact sparse_second_conjugation_root4_column31
  · exact sparse_second_conjugation_root4_column32
  · exact sparse_second_conjugation_root4_column33
  · exact sparse_second_conjugation_root4_column34
  · exact sparse_second_conjugation_root4_column35
  · exact sparse_second_conjugation_root4_column36
  · exact sparse_second_conjugation_root4_column37
  · exact sparse_second_conjugation_root4_column38
  · exact sparse_second_conjugation_root4_column39
  · exact sparse_second_conjugation_root4_column40
  · exact sparse_second_conjugation_root4_column41
  · exact sparse_second_conjugation_root4_column42
  · exact sparse_second_conjugation_root4_column43
  · exact sparse_second_conjugation_root4_column44
  · exact sparse_second_conjugation_root4_column45
  · exact sparse_second_conjugation_root4_column46
  · exact sparse_second_conjugation_root4_column47
  · exact sparse_second_conjugation_root4_column48
  · exact sparse_second_conjugation_root4_column49
  · exact sparse_second_conjugation_root4_column50
  · exact sparse_second_conjugation_root4_column51

theorem simple_commutator_4 : ∀ j : Fin 52,
    simpleMatrix 4 * basisMatrix j - basisMatrix j * simpleMatrix 4 =
      basisCombination (fun k => geckMatrix 4 k j) := by
  intro j
  rw [← denote_geckEntries 4, basisCombination_denote_column]
  simp only [← denote_simpleEntries 4, ← denote_basisEntries j,
    ← denote_product, ← denote_subEntries]
  exact sparse_commutator_root4_all j

theorem simple_second_conjugation_4 : ∀ j : Fin 52,
    simpleSecondMatrix 4 * basisMatrix j + basisMatrix j * simpleSecondMatrix 4 -
      simpleMatrix 4 * basisMatrix j * simpleMatrix 4 =
        basisCombination (fun k => geckSecondMatrix 4 k j) := by
  intro j
  rw [← denote_geckSecondEntries 4, basisCombination_denote_column]
  simp only [← denote_simpleEntries 4, ← denote_simpleSecondEntries 4,
    ← denote_basisEntries j, ← denote_product, ← denote_append,
    ← denote_subEntries]
  exact sparse_second_conjugation_root4_all j

theorem simple_third_conjugation_4 : ∀ j : Fin 52,
    simpleMatrix 4 * basisMatrix j * simpleSecondMatrix 4 -
      simpleSecondMatrix 4 * basisMatrix j * simpleMatrix 4 = 0 := by
  intro j
  simp only [← denote_simpleEntries 4, ← denote_simpleSecondEntries 4, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

theorem simple_fourth_conjugation_4 : ∀ j : Fin 52,
    simpleSecondMatrix 4 * basisMatrix j * simpleSecondMatrix 4 = 0 := by
  intro j
  simp only [← denote_simpleSecondEntries 4, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

end Atlas.Chevalley.Comparison.F4
