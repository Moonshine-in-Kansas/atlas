import F4Work.F4IntegralSparseData
import F4Work.F4SparseBasisCombination

/-! Literal integral identities. No finite-field or group-order certificate. -/
namespace Atlas.Chevalley.Comparison.F4
open scoped Matrix
open Atlas.LinearAlgebra.SparseIntegralMatrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem simple_square_7 :
    simpleMatrix 7 * simpleMatrix 7 = 2 • simpleSecondMatrix 7 := by
  simp only [← denote_simpleEntries 7, ← denote_simpleSecondEntries 7]
  simp only [← denote_product]
  decide +kernel

theorem simple_cube_7 :
    simpleSecondMatrix 7 * simpleMatrix 7 = 0 := by
  simp only [← denote_simpleEntries 7, ← denote_simpleSecondEntries 7]
  simp only [← denote_product]
  decide +kernel

theorem geck_square_7 :
    geckMatrix 7 * geckMatrix 7 = 2 • geckSecondMatrix 7 := by
  simp only [← denote_geckEntries 7, ← denote_geckSecondEntries 7]
  simp only [← denote_product]
  decide +kernel

theorem geck_cube_7 :
    geckSecondMatrix 7 * geckMatrix 7 = 0 := by
  simp only [← denote_geckEntries 7, ← denote_geckSecondEntries 7]
  simp only [← denote_product]
  decide +kernel

/-- Sparse propositions isolate individual column reductions. They use the
existing lists and introduce no new matrix or coefficient table. -/
private abbrev sparseCommutatorRoot7 (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleEntries 7) (basisEntries j))
    (product (basisEntries j) (simpleEntries 7))) =
      denote (columnEntries basisEntries (geckEntries 7) j)

private abbrev sparseSecondConjugationRoot7 (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleSecondEntries 7) (basisEntries j) ++
      product (basisEntries j) (simpleSecondEntries 7))
    (product (product (simpleEntries 7) (basisEntries j)) (simpleEntries 7))) =
      denote (columnEntries basisEntries (geckSecondEntries 7) j)

private theorem sparse_commutator_root7_column0 : sparseCommutatorRoot7 0 := by
  decide +kernel

private theorem sparse_commutator_root7_column1 : sparseCommutatorRoot7 1 := by
  decide +kernel

private theorem sparse_commutator_root7_column2 : sparseCommutatorRoot7 2 := by
  decide +kernel

private theorem sparse_commutator_root7_column3 : sparseCommutatorRoot7 3 := by
  decide +kernel

private theorem sparse_commutator_root7_column4 : sparseCommutatorRoot7 4 := by
  decide +kernel

private theorem sparse_commutator_root7_column5 : sparseCommutatorRoot7 5 := by
  decide +kernel

private theorem sparse_commutator_root7_column6 : sparseCommutatorRoot7 6 := by
  decide +kernel

private theorem sparse_commutator_root7_column7 : sparseCommutatorRoot7 7 := by
  decide +kernel

private theorem sparse_commutator_root7_column8 : sparseCommutatorRoot7 8 := by
  decide +kernel

private theorem sparse_commutator_root7_column9 : sparseCommutatorRoot7 9 := by
  decide +kernel

private theorem sparse_commutator_root7_column10 : sparseCommutatorRoot7 10 := by
  decide +kernel

private theorem sparse_commutator_root7_column11 : sparseCommutatorRoot7 11 := by
  decide +kernel

private theorem sparse_commutator_root7_column12 : sparseCommutatorRoot7 12 := by
  decide +kernel

private theorem sparse_commutator_root7_column13 : sparseCommutatorRoot7 13 := by
  decide +kernel

private theorem sparse_commutator_root7_column14 : sparseCommutatorRoot7 14 := by
  decide +kernel

private theorem sparse_commutator_root7_column15 : sparseCommutatorRoot7 15 := by
  decide +kernel

private theorem sparse_commutator_root7_column16 : sparseCommutatorRoot7 16 := by
  decide +kernel

private theorem sparse_commutator_root7_column17 : sparseCommutatorRoot7 17 := by
  decide +kernel

private theorem sparse_commutator_root7_column18 : sparseCommutatorRoot7 18 := by
  decide +kernel

private theorem sparse_commutator_root7_column19 : sparseCommutatorRoot7 19 := by
  decide +kernel

private theorem sparse_commutator_root7_column20 : sparseCommutatorRoot7 20 := by
  decide +kernel

private theorem sparse_commutator_root7_column21 : sparseCommutatorRoot7 21 := by
  decide +kernel

private theorem sparse_commutator_root7_column22 : sparseCommutatorRoot7 22 := by
  decide +kernel

private theorem sparse_commutator_root7_column23 : sparseCommutatorRoot7 23 := by
  decide +kernel

private theorem sparse_commutator_root7_column24 : sparseCommutatorRoot7 24 := by
  decide +kernel

private theorem sparse_commutator_root7_column25 : sparseCommutatorRoot7 25 := by
  decide +kernel

private theorem sparse_commutator_root7_column26 : sparseCommutatorRoot7 26 := by
  decide +kernel

private theorem sparse_commutator_root7_column27 : sparseCommutatorRoot7 27 := by
  decide +kernel

private theorem sparse_commutator_root7_column28 : sparseCommutatorRoot7 28 := by
  decide +kernel

private theorem sparse_commutator_root7_column29 : sparseCommutatorRoot7 29 := by
  decide +kernel

private theorem sparse_commutator_root7_column30 : sparseCommutatorRoot7 30 := by
  decide +kernel

private theorem sparse_commutator_root7_column31 : sparseCommutatorRoot7 31 := by
  decide +kernel

private theorem sparse_commutator_root7_column32 : sparseCommutatorRoot7 32 := by
  decide +kernel

private theorem sparse_commutator_root7_column33 : sparseCommutatorRoot7 33 := by
  decide +kernel

private theorem sparse_commutator_root7_column34 : sparseCommutatorRoot7 34 := by
  decide +kernel

private theorem sparse_commutator_root7_column35 : sparseCommutatorRoot7 35 := by
  decide +kernel

private theorem sparse_commutator_root7_column36 : sparseCommutatorRoot7 36 := by
  decide +kernel

private theorem sparse_commutator_root7_column37 : sparseCommutatorRoot7 37 := by
  decide +kernel

private theorem sparse_commutator_root7_column38 : sparseCommutatorRoot7 38 := by
  decide +kernel

private theorem sparse_commutator_root7_column39 : sparseCommutatorRoot7 39 := by
  decide +kernel

private theorem sparse_commutator_root7_column40 : sparseCommutatorRoot7 40 := by
  decide +kernel

private theorem sparse_commutator_root7_column41 : sparseCommutatorRoot7 41 := by
  decide +kernel

private theorem sparse_commutator_root7_column42 : sparseCommutatorRoot7 42 := by
  decide +kernel

private theorem sparse_commutator_root7_column43 : sparseCommutatorRoot7 43 := by
  decide +kernel

private theorem sparse_commutator_root7_column44 : sparseCommutatorRoot7 44 := by
  decide +kernel

private theorem sparse_commutator_root7_column45 : sparseCommutatorRoot7 45 := by
  decide +kernel

private theorem sparse_commutator_root7_column46 : sparseCommutatorRoot7 46 := by
  decide +kernel

private theorem sparse_commutator_root7_column47 : sparseCommutatorRoot7 47 := by
  decide +kernel

private theorem sparse_commutator_root7_column48 : sparseCommutatorRoot7 48 := by
  decide +kernel

private theorem sparse_commutator_root7_column49 : sparseCommutatorRoot7 49 := by
  decide +kernel

private theorem sparse_commutator_root7_column50 : sparseCommutatorRoot7 50 := by
  decide +kernel

private theorem sparse_commutator_root7_column51 : sparseCommutatorRoot7 51 := by
  decide +kernel

private theorem sparse_commutator_root7_all (j : Fin 52) : sparseCommutatorRoot7 j := by
  fin_cases j
  · exact sparse_commutator_root7_column0
  · exact sparse_commutator_root7_column1
  · exact sparse_commutator_root7_column2
  · exact sparse_commutator_root7_column3
  · exact sparse_commutator_root7_column4
  · exact sparse_commutator_root7_column5
  · exact sparse_commutator_root7_column6
  · exact sparse_commutator_root7_column7
  · exact sparse_commutator_root7_column8
  · exact sparse_commutator_root7_column9
  · exact sparse_commutator_root7_column10
  · exact sparse_commutator_root7_column11
  · exact sparse_commutator_root7_column12
  · exact sparse_commutator_root7_column13
  · exact sparse_commutator_root7_column14
  · exact sparse_commutator_root7_column15
  · exact sparse_commutator_root7_column16
  · exact sparse_commutator_root7_column17
  · exact sparse_commutator_root7_column18
  · exact sparse_commutator_root7_column19
  · exact sparse_commutator_root7_column20
  · exact sparse_commutator_root7_column21
  · exact sparse_commutator_root7_column22
  · exact sparse_commutator_root7_column23
  · exact sparse_commutator_root7_column24
  · exact sparse_commutator_root7_column25
  · exact sparse_commutator_root7_column26
  · exact sparse_commutator_root7_column27
  · exact sparse_commutator_root7_column28
  · exact sparse_commutator_root7_column29
  · exact sparse_commutator_root7_column30
  · exact sparse_commutator_root7_column31
  · exact sparse_commutator_root7_column32
  · exact sparse_commutator_root7_column33
  · exact sparse_commutator_root7_column34
  · exact sparse_commutator_root7_column35
  · exact sparse_commutator_root7_column36
  · exact sparse_commutator_root7_column37
  · exact sparse_commutator_root7_column38
  · exact sparse_commutator_root7_column39
  · exact sparse_commutator_root7_column40
  · exact sparse_commutator_root7_column41
  · exact sparse_commutator_root7_column42
  · exact sparse_commutator_root7_column43
  · exact sparse_commutator_root7_column44
  · exact sparse_commutator_root7_column45
  · exact sparse_commutator_root7_column46
  · exact sparse_commutator_root7_column47
  · exact sparse_commutator_root7_column48
  · exact sparse_commutator_root7_column49
  · exact sparse_commutator_root7_column50
  · exact sparse_commutator_root7_column51

private theorem sparse_second_conjugation_root7_column0 : sparseSecondConjugationRoot7 0 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column1 : sparseSecondConjugationRoot7 1 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column2 : sparseSecondConjugationRoot7 2 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column3 : sparseSecondConjugationRoot7 3 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column4 : sparseSecondConjugationRoot7 4 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column5 : sparseSecondConjugationRoot7 5 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column6 : sparseSecondConjugationRoot7 6 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column7 : sparseSecondConjugationRoot7 7 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column8 : sparseSecondConjugationRoot7 8 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column9 : sparseSecondConjugationRoot7 9 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column10 : sparseSecondConjugationRoot7 10 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column11 : sparseSecondConjugationRoot7 11 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column12 : sparseSecondConjugationRoot7 12 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column13 : sparseSecondConjugationRoot7 13 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column14 : sparseSecondConjugationRoot7 14 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column15 : sparseSecondConjugationRoot7 15 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column16 : sparseSecondConjugationRoot7 16 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column17 : sparseSecondConjugationRoot7 17 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column18 : sparseSecondConjugationRoot7 18 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column19 : sparseSecondConjugationRoot7 19 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column20 : sparseSecondConjugationRoot7 20 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column21 : sparseSecondConjugationRoot7 21 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column22 : sparseSecondConjugationRoot7 22 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column23 : sparseSecondConjugationRoot7 23 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column24 : sparseSecondConjugationRoot7 24 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column25 : sparseSecondConjugationRoot7 25 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column26 : sparseSecondConjugationRoot7 26 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column27 : sparseSecondConjugationRoot7 27 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column28 : sparseSecondConjugationRoot7 28 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column29 : sparseSecondConjugationRoot7 29 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column30 : sparseSecondConjugationRoot7 30 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column31 : sparseSecondConjugationRoot7 31 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column32 : sparseSecondConjugationRoot7 32 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column33 : sparseSecondConjugationRoot7 33 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column34 : sparseSecondConjugationRoot7 34 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column35 : sparseSecondConjugationRoot7 35 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column36 : sparseSecondConjugationRoot7 36 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column37 : sparseSecondConjugationRoot7 37 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column38 : sparseSecondConjugationRoot7 38 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column39 : sparseSecondConjugationRoot7 39 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column40 : sparseSecondConjugationRoot7 40 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column41 : sparseSecondConjugationRoot7 41 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column42 : sparseSecondConjugationRoot7 42 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column43 : sparseSecondConjugationRoot7 43 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column44 : sparseSecondConjugationRoot7 44 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column45 : sparseSecondConjugationRoot7 45 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column46 : sparseSecondConjugationRoot7 46 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column47 : sparseSecondConjugationRoot7 47 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column48 : sparseSecondConjugationRoot7 48 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column49 : sparseSecondConjugationRoot7 49 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column50 : sparseSecondConjugationRoot7 50 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_column51 : sparseSecondConjugationRoot7 51 := by
  decide +kernel

private theorem sparse_second_conjugation_root7_all (j : Fin 52) : sparseSecondConjugationRoot7 j := by
  fin_cases j
  · exact sparse_second_conjugation_root7_column0
  · exact sparse_second_conjugation_root7_column1
  · exact sparse_second_conjugation_root7_column2
  · exact sparse_second_conjugation_root7_column3
  · exact sparse_second_conjugation_root7_column4
  · exact sparse_second_conjugation_root7_column5
  · exact sparse_second_conjugation_root7_column6
  · exact sparse_second_conjugation_root7_column7
  · exact sparse_second_conjugation_root7_column8
  · exact sparse_second_conjugation_root7_column9
  · exact sparse_second_conjugation_root7_column10
  · exact sparse_second_conjugation_root7_column11
  · exact sparse_second_conjugation_root7_column12
  · exact sparse_second_conjugation_root7_column13
  · exact sparse_second_conjugation_root7_column14
  · exact sparse_second_conjugation_root7_column15
  · exact sparse_second_conjugation_root7_column16
  · exact sparse_second_conjugation_root7_column17
  · exact sparse_second_conjugation_root7_column18
  · exact sparse_second_conjugation_root7_column19
  · exact sparse_second_conjugation_root7_column20
  · exact sparse_second_conjugation_root7_column21
  · exact sparse_second_conjugation_root7_column22
  · exact sparse_second_conjugation_root7_column23
  · exact sparse_second_conjugation_root7_column24
  · exact sparse_second_conjugation_root7_column25
  · exact sparse_second_conjugation_root7_column26
  · exact sparse_second_conjugation_root7_column27
  · exact sparse_second_conjugation_root7_column28
  · exact sparse_second_conjugation_root7_column29
  · exact sparse_second_conjugation_root7_column30
  · exact sparse_second_conjugation_root7_column31
  · exact sparse_second_conjugation_root7_column32
  · exact sparse_second_conjugation_root7_column33
  · exact sparse_second_conjugation_root7_column34
  · exact sparse_second_conjugation_root7_column35
  · exact sparse_second_conjugation_root7_column36
  · exact sparse_second_conjugation_root7_column37
  · exact sparse_second_conjugation_root7_column38
  · exact sparse_second_conjugation_root7_column39
  · exact sparse_second_conjugation_root7_column40
  · exact sparse_second_conjugation_root7_column41
  · exact sparse_second_conjugation_root7_column42
  · exact sparse_second_conjugation_root7_column43
  · exact sparse_second_conjugation_root7_column44
  · exact sparse_second_conjugation_root7_column45
  · exact sparse_second_conjugation_root7_column46
  · exact sparse_second_conjugation_root7_column47
  · exact sparse_second_conjugation_root7_column48
  · exact sparse_second_conjugation_root7_column49
  · exact sparse_second_conjugation_root7_column50
  · exact sparse_second_conjugation_root7_column51

theorem simple_commutator_7 : ∀ j : Fin 52,
    simpleMatrix 7 * basisMatrix j - basisMatrix j * simpleMatrix 7 =
      basisCombination (fun k => geckMatrix 7 k j) := by
  intro j
  rw [← denote_geckEntries 7, basisCombination_denote_column]
  simp only [← denote_simpleEntries 7, ← denote_basisEntries j,
    ← denote_product, ← denote_subEntries]
  exact sparse_commutator_root7_all j

theorem simple_second_conjugation_7 : ∀ j : Fin 52,
    simpleSecondMatrix 7 * basisMatrix j + basisMatrix j * simpleSecondMatrix 7 -
      simpleMatrix 7 * basisMatrix j * simpleMatrix 7 =
        basisCombination (fun k => geckSecondMatrix 7 k j) := by
  intro j
  rw [← denote_geckSecondEntries 7, basisCombination_denote_column]
  simp only [← denote_simpleEntries 7, ← denote_simpleSecondEntries 7,
    ← denote_basisEntries j, ← denote_product, ← denote_append,
    ← denote_subEntries]
  exact sparse_second_conjugation_root7_all j

theorem simple_third_conjugation_7 : ∀ j : Fin 52,
    simpleMatrix 7 * basisMatrix j * simpleSecondMatrix 7 -
      simpleSecondMatrix 7 * basisMatrix j * simpleMatrix 7 = 0 := by
  intro j
  simp only [← denote_simpleEntries 7, ← denote_simpleSecondEntries 7, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

theorem simple_fourth_conjugation_7 : ∀ j : Fin 52,
    simpleSecondMatrix 7 * basisMatrix j * simpleSecondMatrix 7 = 0 := by
  intro j
  simp only [← denote_simpleSecondEntries 7, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

end Atlas.Chevalley.Comparison.F4
