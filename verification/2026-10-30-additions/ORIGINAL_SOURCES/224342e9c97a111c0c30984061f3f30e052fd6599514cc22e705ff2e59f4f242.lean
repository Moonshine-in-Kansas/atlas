import F4Work.F4IntegralSparseData
import F4Work.F4SparseBasisCombination

/-! Literal integral identities. No finite-field or group-order certificate. -/
namespace Atlas.Chevalley.Comparison.F4
open scoped Matrix
open Atlas.LinearAlgebra.SparseIntegralMatrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem simple_square_3 :
    simpleMatrix 3 * simpleMatrix 3 = 2 • simpleSecondMatrix 3 := by
  simp only [← denote_simpleEntries 3, ← denote_simpleSecondEntries 3]
  simp only [← denote_product]
  decide +kernel

theorem simple_cube_3 :
    simpleSecondMatrix 3 * simpleMatrix 3 = 0 := by
  simp only [← denote_simpleEntries 3, ← denote_simpleSecondEntries 3]
  simp only [← denote_product]
  decide +kernel

theorem geck_square_3 :
    geckMatrix 3 * geckMatrix 3 = 2 • geckSecondMatrix 3 := by
  simp only [← denote_geckEntries 3, ← denote_geckSecondEntries 3]
  simp only [← denote_product]
  decide +kernel

theorem geck_cube_3 :
    geckSecondMatrix 3 * geckMatrix 3 = 0 := by
  simp only [← denote_geckEntries 3, ← denote_geckSecondEntries 3]
  simp only [← denote_product]
  decide +kernel

/-- Sparse propositions isolate individual column reductions. They use the
existing lists and introduce no new matrix or coefficient table. -/
private abbrev sparseCommutatorRoot3 (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleEntries 3) (basisEntries j))
    (product (basisEntries j) (simpleEntries 3))) =
      denote (columnEntries basisEntries (geckEntries 3) j)

private abbrev sparseSecondConjugationRoot3 (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleSecondEntries 3) (basisEntries j) ++
      product (basisEntries j) (simpleSecondEntries 3))
    (product (product (simpleEntries 3) (basisEntries j)) (simpleEntries 3))) =
      denote (columnEntries basisEntries (geckSecondEntries 3) j)

private theorem sparse_commutator_root3_column0 : sparseCommutatorRoot3 0 := by
  decide +kernel

private theorem sparse_commutator_root3_column1 : sparseCommutatorRoot3 1 := by
  decide +kernel

private theorem sparse_commutator_root3_column2 : sparseCommutatorRoot3 2 := by
  decide +kernel

private theorem sparse_commutator_root3_column3 : sparseCommutatorRoot3 3 := by
  decide +kernel

private theorem sparse_commutator_root3_column4 : sparseCommutatorRoot3 4 := by
  decide +kernel

private theorem sparse_commutator_root3_column5 : sparseCommutatorRoot3 5 := by
  decide +kernel

private theorem sparse_commutator_root3_column6 : sparseCommutatorRoot3 6 := by
  decide +kernel

private theorem sparse_commutator_root3_column7 : sparseCommutatorRoot3 7 := by
  decide +kernel

private theorem sparse_commutator_root3_column8 : sparseCommutatorRoot3 8 := by
  decide +kernel

private theorem sparse_commutator_root3_column9 : sparseCommutatorRoot3 9 := by
  decide +kernel

private theorem sparse_commutator_root3_column10 : sparseCommutatorRoot3 10 := by
  decide +kernel

private theorem sparse_commutator_root3_column11 : sparseCommutatorRoot3 11 := by
  decide +kernel

private theorem sparse_commutator_root3_column12 : sparseCommutatorRoot3 12 := by
  decide +kernel

private theorem sparse_commutator_root3_column13 : sparseCommutatorRoot3 13 := by
  decide +kernel

private theorem sparse_commutator_root3_column14 : sparseCommutatorRoot3 14 := by
  decide +kernel

private theorem sparse_commutator_root3_column15 : sparseCommutatorRoot3 15 := by
  decide +kernel

private theorem sparse_commutator_root3_column16 : sparseCommutatorRoot3 16 := by
  decide +kernel

private theorem sparse_commutator_root3_column17 : sparseCommutatorRoot3 17 := by
  decide +kernel

private theorem sparse_commutator_root3_column18 : sparseCommutatorRoot3 18 := by
  decide +kernel

private theorem sparse_commutator_root3_column19 : sparseCommutatorRoot3 19 := by
  decide +kernel

private theorem sparse_commutator_root3_column20 : sparseCommutatorRoot3 20 := by
  decide +kernel

private theorem sparse_commutator_root3_column21 : sparseCommutatorRoot3 21 := by
  decide +kernel

private theorem sparse_commutator_root3_column22 : sparseCommutatorRoot3 22 := by
  decide +kernel

private theorem sparse_commutator_root3_column23 : sparseCommutatorRoot3 23 := by
  decide +kernel

private theorem sparse_commutator_root3_column24 : sparseCommutatorRoot3 24 := by
  decide +kernel

private theorem sparse_commutator_root3_column25 : sparseCommutatorRoot3 25 := by
  decide +kernel

private theorem sparse_commutator_root3_column26 : sparseCommutatorRoot3 26 := by
  decide +kernel

private theorem sparse_commutator_root3_column27 : sparseCommutatorRoot3 27 := by
  decide +kernel

private theorem sparse_commutator_root3_column28 : sparseCommutatorRoot3 28 := by
  decide +kernel

private theorem sparse_commutator_root3_column29 : sparseCommutatorRoot3 29 := by
  decide +kernel

private theorem sparse_commutator_root3_column30 : sparseCommutatorRoot3 30 := by
  decide +kernel

private theorem sparse_commutator_root3_column31 : sparseCommutatorRoot3 31 := by
  decide +kernel

private theorem sparse_commutator_root3_column32 : sparseCommutatorRoot3 32 := by
  decide +kernel

private theorem sparse_commutator_root3_column33 : sparseCommutatorRoot3 33 := by
  decide +kernel

private theorem sparse_commutator_root3_column34 : sparseCommutatorRoot3 34 := by
  decide +kernel

private theorem sparse_commutator_root3_column35 : sparseCommutatorRoot3 35 := by
  decide +kernel

private theorem sparse_commutator_root3_column36 : sparseCommutatorRoot3 36 := by
  decide +kernel

private theorem sparse_commutator_root3_column37 : sparseCommutatorRoot3 37 := by
  decide +kernel

private theorem sparse_commutator_root3_column38 : sparseCommutatorRoot3 38 := by
  decide +kernel

private theorem sparse_commutator_root3_column39 : sparseCommutatorRoot3 39 := by
  decide +kernel

private theorem sparse_commutator_root3_column40 : sparseCommutatorRoot3 40 := by
  decide +kernel

private theorem sparse_commutator_root3_column41 : sparseCommutatorRoot3 41 := by
  decide +kernel

private theorem sparse_commutator_root3_column42 : sparseCommutatorRoot3 42 := by
  decide +kernel

private theorem sparse_commutator_root3_column43 : sparseCommutatorRoot3 43 := by
  decide +kernel

private theorem sparse_commutator_root3_column44 : sparseCommutatorRoot3 44 := by
  decide +kernel

private theorem sparse_commutator_root3_column45 : sparseCommutatorRoot3 45 := by
  decide +kernel

private theorem sparse_commutator_root3_column46 : sparseCommutatorRoot3 46 := by
  decide +kernel

private theorem sparse_commutator_root3_column47 : sparseCommutatorRoot3 47 := by
  decide +kernel

private theorem sparse_commutator_root3_column48 : sparseCommutatorRoot3 48 := by
  decide +kernel

private theorem sparse_commutator_root3_column49 : sparseCommutatorRoot3 49 := by
  decide +kernel

private theorem sparse_commutator_root3_column50 : sparseCommutatorRoot3 50 := by
  decide +kernel

private theorem sparse_commutator_root3_column51 : sparseCommutatorRoot3 51 := by
  decide +kernel

private theorem sparse_commutator_root3_all (j : Fin 52) : sparseCommutatorRoot3 j := by
  fin_cases j
  · exact sparse_commutator_root3_column0
  · exact sparse_commutator_root3_column1
  · exact sparse_commutator_root3_column2
  · exact sparse_commutator_root3_column3
  · exact sparse_commutator_root3_column4
  · exact sparse_commutator_root3_column5
  · exact sparse_commutator_root3_column6
  · exact sparse_commutator_root3_column7
  · exact sparse_commutator_root3_column8
  · exact sparse_commutator_root3_column9
  · exact sparse_commutator_root3_column10
  · exact sparse_commutator_root3_column11
  · exact sparse_commutator_root3_column12
  · exact sparse_commutator_root3_column13
  · exact sparse_commutator_root3_column14
  · exact sparse_commutator_root3_column15
  · exact sparse_commutator_root3_column16
  · exact sparse_commutator_root3_column17
  · exact sparse_commutator_root3_column18
  · exact sparse_commutator_root3_column19
  · exact sparse_commutator_root3_column20
  · exact sparse_commutator_root3_column21
  · exact sparse_commutator_root3_column22
  · exact sparse_commutator_root3_column23
  · exact sparse_commutator_root3_column24
  · exact sparse_commutator_root3_column25
  · exact sparse_commutator_root3_column26
  · exact sparse_commutator_root3_column27
  · exact sparse_commutator_root3_column28
  · exact sparse_commutator_root3_column29
  · exact sparse_commutator_root3_column30
  · exact sparse_commutator_root3_column31
  · exact sparse_commutator_root3_column32
  · exact sparse_commutator_root3_column33
  · exact sparse_commutator_root3_column34
  · exact sparse_commutator_root3_column35
  · exact sparse_commutator_root3_column36
  · exact sparse_commutator_root3_column37
  · exact sparse_commutator_root3_column38
  · exact sparse_commutator_root3_column39
  · exact sparse_commutator_root3_column40
  · exact sparse_commutator_root3_column41
  · exact sparse_commutator_root3_column42
  · exact sparse_commutator_root3_column43
  · exact sparse_commutator_root3_column44
  · exact sparse_commutator_root3_column45
  · exact sparse_commutator_root3_column46
  · exact sparse_commutator_root3_column47
  · exact sparse_commutator_root3_column48
  · exact sparse_commutator_root3_column49
  · exact sparse_commutator_root3_column50
  · exact sparse_commutator_root3_column51

private theorem sparse_second_conjugation_root3_column0 : sparseSecondConjugationRoot3 0 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column1 : sparseSecondConjugationRoot3 1 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column2 : sparseSecondConjugationRoot3 2 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column3 : sparseSecondConjugationRoot3 3 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column4 : sparseSecondConjugationRoot3 4 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column5 : sparseSecondConjugationRoot3 5 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column6 : sparseSecondConjugationRoot3 6 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column7 : sparseSecondConjugationRoot3 7 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column8 : sparseSecondConjugationRoot3 8 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column9 : sparseSecondConjugationRoot3 9 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column10 : sparseSecondConjugationRoot3 10 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column11 : sparseSecondConjugationRoot3 11 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column12 : sparseSecondConjugationRoot3 12 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column13 : sparseSecondConjugationRoot3 13 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column14 : sparseSecondConjugationRoot3 14 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column15 : sparseSecondConjugationRoot3 15 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column16 : sparseSecondConjugationRoot3 16 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column17 : sparseSecondConjugationRoot3 17 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column18 : sparseSecondConjugationRoot3 18 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column19 : sparseSecondConjugationRoot3 19 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column20 : sparseSecondConjugationRoot3 20 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column21 : sparseSecondConjugationRoot3 21 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column22 : sparseSecondConjugationRoot3 22 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column23 : sparseSecondConjugationRoot3 23 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column24 : sparseSecondConjugationRoot3 24 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column25 : sparseSecondConjugationRoot3 25 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column26 : sparseSecondConjugationRoot3 26 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column27 : sparseSecondConjugationRoot3 27 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column28 : sparseSecondConjugationRoot3 28 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column29 : sparseSecondConjugationRoot3 29 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column30 : sparseSecondConjugationRoot3 30 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column31 : sparseSecondConjugationRoot3 31 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column32 : sparseSecondConjugationRoot3 32 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column33 : sparseSecondConjugationRoot3 33 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column34 : sparseSecondConjugationRoot3 34 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column35 : sparseSecondConjugationRoot3 35 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column36 : sparseSecondConjugationRoot3 36 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column37 : sparseSecondConjugationRoot3 37 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column38 : sparseSecondConjugationRoot3 38 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column39 : sparseSecondConjugationRoot3 39 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column40 : sparseSecondConjugationRoot3 40 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column41 : sparseSecondConjugationRoot3 41 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column42 : sparseSecondConjugationRoot3 42 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column43 : sparseSecondConjugationRoot3 43 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column44 : sparseSecondConjugationRoot3 44 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column45 : sparseSecondConjugationRoot3 45 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column46 : sparseSecondConjugationRoot3 46 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column47 : sparseSecondConjugationRoot3 47 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column48 : sparseSecondConjugationRoot3 48 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column49 : sparseSecondConjugationRoot3 49 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column50 : sparseSecondConjugationRoot3 50 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_column51 : sparseSecondConjugationRoot3 51 := by
  decide +kernel

private theorem sparse_second_conjugation_root3_all (j : Fin 52) : sparseSecondConjugationRoot3 j := by
  fin_cases j
  · exact sparse_second_conjugation_root3_column0
  · exact sparse_second_conjugation_root3_column1
  · exact sparse_second_conjugation_root3_column2
  · exact sparse_second_conjugation_root3_column3
  · exact sparse_second_conjugation_root3_column4
  · exact sparse_second_conjugation_root3_column5
  · exact sparse_second_conjugation_root3_column6
  · exact sparse_second_conjugation_root3_column7
  · exact sparse_second_conjugation_root3_column8
  · exact sparse_second_conjugation_root3_column9
  · exact sparse_second_conjugation_root3_column10
  · exact sparse_second_conjugation_root3_column11
  · exact sparse_second_conjugation_root3_column12
  · exact sparse_second_conjugation_root3_column13
  · exact sparse_second_conjugation_root3_column14
  · exact sparse_second_conjugation_root3_column15
  · exact sparse_second_conjugation_root3_column16
  · exact sparse_second_conjugation_root3_column17
  · exact sparse_second_conjugation_root3_column18
  · exact sparse_second_conjugation_root3_column19
  · exact sparse_second_conjugation_root3_column20
  · exact sparse_second_conjugation_root3_column21
  · exact sparse_second_conjugation_root3_column22
  · exact sparse_second_conjugation_root3_column23
  · exact sparse_second_conjugation_root3_column24
  · exact sparse_second_conjugation_root3_column25
  · exact sparse_second_conjugation_root3_column26
  · exact sparse_second_conjugation_root3_column27
  · exact sparse_second_conjugation_root3_column28
  · exact sparse_second_conjugation_root3_column29
  · exact sparse_second_conjugation_root3_column30
  · exact sparse_second_conjugation_root3_column31
  · exact sparse_second_conjugation_root3_column32
  · exact sparse_second_conjugation_root3_column33
  · exact sparse_second_conjugation_root3_column34
  · exact sparse_second_conjugation_root3_column35
  · exact sparse_second_conjugation_root3_column36
  · exact sparse_second_conjugation_root3_column37
  · exact sparse_second_conjugation_root3_column38
  · exact sparse_second_conjugation_root3_column39
  · exact sparse_second_conjugation_root3_column40
  · exact sparse_second_conjugation_root3_column41
  · exact sparse_second_conjugation_root3_column42
  · exact sparse_second_conjugation_root3_column43
  · exact sparse_second_conjugation_root3_column44
  · exact sparse_second_conjugation_root3_column45
  · exact sparse_second_conjugation_root3_column46
  · exact sparse_second_conjugation_root3_column47
  · exact sparse_second_conjugation_root3_column48
  · exact sparse_second_conjugation_root3_column49
  · exact sparse_second_conjugation_root3_column50
  · exact sparse_second_conjugation_root3_column51

theorem simple_commutator_3 : ∀ j : Fin 52,
    simpleMatrix 3 * basisMatrix j - basisMatrix j * simpleMatrix 3 =
      basisCombination (fun k => geckMatrix 3 k j) := by
  intro j
  rw [← denote_geckEntries 3, basisCombination_denote_column]
  simp only [← denote_simpleEntries 3, ← denote_basisEntries j,
    ← denote_product, ← denote_subEntries]
  exact sparse_commutator_root3_all j

theorem simple_second_conjugation_3 : ∀ j : Fin 52,
    simpleSecondMatrix 3 * basisMatrix j + basisMatrix j * simpleSecondMatrix 3 -
      simpleMatrix 3 * basisMatrix j * simpleMatrix 3 =
        basisCombination (fun k => geckSecondMatrix 3 k j) := by
  intro j
  rw [← denote_geckSecondEntries 3, basisCombination_denote_column]
  simp only [← denote_simpleEntries 3, ← denote_simpleSecondEntries 3,
    ← denote_basisEntries j, ← denote_product, ← denote_append,
    ← denote_subEntries]
  exact sparse_second_conjugation_root3_all j

theorem simple_third_conjugation_3 : ∀ j : Fin 52,
    simpleMatrix 3 * basisMatrix j * simpleSecondMatrix 3 -
      simpleSecondMatrix 3 * basisMatrix j * simpleMatrix 3 = 0 := by
  intro j
  simp only [← denote_simpleEntries 3, ← denote_simpleSecondEntries 3, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

theorem simple_fourth_conjugation_3 : ∀ j : Fin 52,
    simpleSecondMatrix 3 * basisMatrix j * simpleSecondMatrix 3 = 0 := by
  intro j
  simp only [← denote_simpleSecondEntries 3, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

end Atlas.Chevalley.Comparison.F4
