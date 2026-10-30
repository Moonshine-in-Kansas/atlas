import F4Work.F4IntegralSparseData
import F4Work.F4SparseBasisCombination

/-! Literal integral identities. No finite-field or group-order certificate. -/
namespace Atlas.Chevalley.Comparison.F4
open scoped Matrix
open Atlas.LinearAlgebra.SparseIntegralMatrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem simple_square_5 :
    simpleMatrix 5 * simpleMatrix 5 = 2 • simpleSecondMatrix 5 := by
  simp only [← denote_simpleEntries 5, ← denote_simpleSecondEntries 5]
  simp only [← denote_product]
  decide +kernel

theorem simple_cube_5 :
    simpleSecondMatrix 5 * simpleMatrix 5 = 0 := by
  simp only [← denote_simpleEntries 5, ← denote_simpleSecondEntries 5]
  simp only [← denote_product]
  decide +kernel

theorem geck_square_5 :
    geckMatrix 5 * geckMatrix 5 = 2 • geckSecondMatrix 5 := by
  simp only [← denote_geckEntries 5, ← denote_geckSecondEntries 5]
  simp only [← denote_product]
  decide +kernel

theorem geck_cube_5 :
    geckSecondMatrix 5 * geckMatrix 5 = 0 := by
  simp only [← denote_geckEntries 5, ← denote_geckSecondEntries 5]
  simp only [← denote_product]
  decide +kernel

/-- Sparse propositions isolate individual column reductions. They use the
existing lists and introduce no new matrix or coefficient table. -/
private abbrev sparseCommutatorRoot5 (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleEntries 5) (basisEntries j))
    (product (basisEntries j) (simpleEntries 5))) =
      denote (columnEntries basisEntries (geckEntries 5) j)

private abbrev sparseSecondConjugationRoot5 (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleSecondEntries 5) (basisEntries j) ++
      product (basisEntries j) (simpleSecondEntries 5))
    (product (product (simpleEntries 5) (basisEntries j)) (simpleEntries 5))) =
      denote (columnEntries basisEntries (geckSecondEntries 5) j)

private theorem sparse_commutator_root5_column0 : sparseCommutatorRoot5 0 := by
  decide +kernel

private theorem sparse_commutator_root5_column1 : sparseCommutatorRoot5 1 := by
  decide +kernel

private theorem sparse_commutator_root5_column2 : sparseCommutatorRoot5 2 := by
  decide +kernel

private theorem sparse_commutator_root5_column3 : sparseCommutatorRoot5 3 := by
  decide +kernel

private theorem sparse_commutator_root5_column4 : sparseCommutatorRoot5 4 := by
  decide +kernel

private theorem sparse_commutator_root5_column5 : sparseCommutatorRoot5 5 := by
  decide +kernel

private theorem sparse_commutator_root5_column6 : sparseCommutatorRoot5 6 := by
  decide +kernel

private theorem sparse_commutator_root5_column7 : sparseCommutatorRoot5 7 := by
  decide +kernel

private theorem sparse_commutator_root5_column8 : sparseCommutatorRoot5 8 := by
  decide +kernel

private theorem sparse_commutator_root5_column9 : sparseCommutatorRoot5 9 := by
  decide +kernel

private theorem sparse_commutator_root5_column10 : sparseCommutatorRoot5 10 := by
  decide +kernel

private theorem sparse_commutator_root5_column11 : sparseCommutatorRoot5 11 := by
  decide +kernel

private theorem sparse_commutator_root5_column12 : sparseCommutatorRoot5 12 := by
  decide +kernel

private theorem sparse_commutator_root5_column13 : sparseCommutatorRoot5 13 := by
  decide +kernel

private theorem sparse_commutator_root5_column14 : sparseCommutatorRoot5 14 := by
  decide +kernel

private theorem sparse_commutator_root5_column15 : sparseCommutatorRoot5 15 := by
  decide +kernel

private theorem sparse_commutator_root5_column16 : sparseCommutatorRoot5 16 := by
  decide +kernel

private theorem sparse_commutator_root5_column17 : sparseCommutatorRoot5 17 := by
  decide +kernel

private theorem sparse_commutator_root5_column18 : sparseCommutatorRoot5 18 := by
  decide +kernel

private theorem sparse_commutator_root5_column19 : sparseCommutatorRoot5 19 := by
  decide +kernel

private theorem sparse_commutator_root5_column20 : sparseCommutatorRoot5 20 := by
  decide +kernel

private theorem sparse_commutator_root5_column21 : sparseCommutatorRoot5 21 := by
  decide +kernel

private theorem sparse_commutator_root5_column22 : sparseCommutatorRoot5 22 := by
  decide +kernel

private theorem sparse_commutator_root5_column23 : sparseCommutatorRoot5 23 := by
  decide +kernel

private theorem sparse_commutator_root5_column24 : sparseCommutatorRoot5 24 := by
  decide +kernel

private theorem sparse_commutator_root5_column25 : sparseCommutatorRoot5 25 := by
  decide +kernel

private theorem sparse_commutator_root5_column26 : sparseCommutatorRoot5 26 := by
  decide +kernel

private theorem sparse_commutator_root5_column27 : sparseCommutatorRoot5 27 := by
  decide +kernel

private theorem sparse_commutator_root5_column28 : sparseCommutatorRoot5 28 := by
  decide +kernel

private theorem sparse_commutator_root5_column29 : sparseCommutatorRoot5 29 := by
  decide +kernel

private theorem sparse_commutator_root5_column30 : sparseCommutatorRoot5 30 := by
  decide +kernel

private theorem sparse_commutator_root5_column31 : sparseCommutatorRoot5 31 := by
  decide +kernel

private theorem sparse_commutator_root5_column32 : sparseCommutatorRoot5 32 := by
  decide +kernel

private theorem sparse_commutator_root5_column33 : sparseCommutatorRoot5 33 := by
  decide +kernel

private theorem sparse_commutator_root5_column34 : sparseCommutatorRoot5 34 := by
  decide +kernel

private theorem sparse_commutator_root5_column35 : sparseCommutatorRoot5 35 := by
  decide +kernel

private theorem sparse_commutator_root5_column36 : sparseCommutatorRoot5 36 := by
  decide +kernel

private theorem sparse_commutator_root5_column37 : sparseCommutatorRoot5 37 := by
  decide +kernel

private theorem sparse_commutator_root5_column38 : sparseCommutatorRoot5 38 := by
  decide +kernel

private theorem sparse_commutator_root5_column39 : sparseCommutatorRoot5 39 := by
  decide +kernel

private theorem sparse_commutator_root5_column40 : sparseCommutatorRoot5 40 := by
  decide +kernel

private theorem sparse_commutator_root5_column41 : sparseCommutatorRoot5 41 := by
  decide +kernel

private theorem sparse_commutator_root5_column42 : sparseCommutatorRoot5 42 := by
  decide +kernel

private theorem sparse_commutator_root5_column43 : sparseCommutatorRoot5 43 := by
  decide +kernel

private theorem sparse_commutator_root5_column44 : sparseCommutatorRoot5 44 := by
  decide +kernel

private theorem sparse_commutator_root5_column45 : sparseCommutatorRoot5 45 := by
  decide +kernel

private theorem sparse_commutator_root5_column46 : sparseCommutatorRoot5 46 := by
  decide +kernel

private theorem sparse_commutator_root5_column47 : sparseCommutatorRoot5 47 := by
  decide +kernel

private theorem sparse_commutator_root5_column48 : sparseCommutatorRoot5 48 := by
  decide +kernel

private theorem sparse_commutator_root5_column49 : sparseCommutatorRoot5 49 := by
  decide +kernel

private theorem sparse_commutator_root5_column50 : sparseCommutatorRoot5 50 := by
  decide +kernel

private theorem sparse_commutator_root5_column51 : sparseCommutatorRoot5 51 := by
  decide +kernel

private theorem sparse_commutator_root5_all (j : Fin 52) : sparseCommutatorRoot5 j := by
  fin_cases j
  · exact sparse_commutator_root5_column0
  · exact sparse_commutator_root5_column1
  · exact sparse_commutator_root5_column2
  · exact sparse_commutator_root5_column3
  · exact sparse_commutator_root5_column4
  · exact sparse_commutator_root5_column5
  · exact sparse_commutator_root5_column6
  · exact sparse_commutator_root5_column7
  · exact sparse_commutator_root5_column8
  · exact sparse_commutator_root5_column9
  · exact sparse_commutator_root5_column10
  · exact sparse_commutator_root5_column11
  · exact sparse_commutator_root5_column12
  · exact sparse_commutator_root5_column13
  · exact sparse_commutator_root5_column14
  · exact sparse_commutator_root5_column15
  · exact sparse_commutator_root5_column16
  · exact sparse_commutator_root5_column17
  · exact sparse_commutator_root5_column18
  · exact sparse_commutator_root5_column19
  · exact sparse_commutator_root5_column20
  · exact sparse_commutator_root5_column21
  · exact sparse_commutator_root5_column22
  · exact sparse_commutator_root5_column23
  · exact sparse_commutator_root5_column24
  · exact sparse_commutator_root5_column25
  · exact sparse_commutator_root5_column26
  · exact sparse_commutator_root5_column27
  · exact sparse_commutator_root5_column28
  · exact sparse_commutator_root5_column29
  · exact sparse_commutator_root5_column30
  · exact sparse_commutator_root5_column31
  · exact sparse_commutator_root5_column32
  · exact sparse_commutator_root5_column33
  · exact sparse_commutator_root5_column34
  · exact sparse_commutator_root5_column35
  · exact sparse_commutator_root5_column36
  · exact sparse_commutator_root5_column37
  · exact sparse_commutator_root5_column38
  · exact sparse_commutator_root5_column39
  · exact sparse_commutator_root5_column40
  · exact sparse_commutator_root5_column41
  · exact sparse_commutator_root5_column42
  · exact sparse_commutator_root5_column43
  · exact sparse_commutator_root5_column44
  · exact sparse_commutator_root5_column45
  · exact sparse_commutator_root5_column46
  · exact sparse_commutator_root5_column47
  · exact sparse_commutator_root5_column48
  · exact sparse_commutator_root5_column49
  · exact sparse_commutator_root5_column50
  · exact sparse_commutator_root5_column51

private theorem sparse_second_conjugation_root5_column0 : sparseSecondConjugationRoot5 0 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column1 : sparseSecondConjugationRoot5 1 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column2 : sparseSecondConjugationRoot5 2 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column3 : sparseSecondConjugationRoot5 3 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column4 : sparseSecondConjugationRoot5 4 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column5 : sparseSecondConjugationRoot5 5 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column6 : sparseSecondConjugationRoot5 6 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column7 : sparseSecondConjugationRoot5 7 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column8 : sparseSecondConjugationRoot5 8 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column9 : sparseSecondConjugationRoot5 9 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column10 : sparseSecondConjugationRoot5 10 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column11 : sparseSecondConjugationRoot5 11 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column12 : sparseSecondConjugationRoot5 12 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column13 : sparseSecondConjugationRoot5 13 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column14 : sparseSecondConjugationRoot5 14 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column15 : sparseSecondConjugationRoot5 15 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column16 : sparseSecondConjugationRoot5 16 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column17 : sparseSecondConjugationRoot5 17 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column18 : sparseSecondConjugationRoot5 18 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column19 : sparseSecondConjugationRoot5 19 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column20 : sparseSecondConjugationRoot5 20 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column21 : sparseSecondConjugationRoot5 21 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column22 : sparseSecondConjugationRoot5 22 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column23 : sparseSecondConjugationRoot5 23 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column24 : sparseSecondConjugationRoot5 24 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column25 : sparseSecondConjugationRoot5 25 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column26 : sparseSecondConjugationRoot5 26 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column27 : sparseSecondConjugationRoot5 27 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column28 : sparseSecondConjugationRoot5 28 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column29 : sparseSecondConjugationRoot5 29 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column30 : sparseSecondConjugationRoot5 30 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column31 : sparseSecondConjugationRoot5 31 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column32 : sparseSecondConjugationRoot5 32 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column33 : sparseSecondConjugationRoot5 33 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column34 : sparseSecondConjugationRoot5 34 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column35 : sparseSecondConjugationRoot5 35 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column36 : sparseSecondConjugationRoot5 36 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column37 : sparseSecondConjugationRoot5 37 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column38 : sparseSecondConjugationRoot5 38 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column39 : sparseSecondConjugationRoot5 39 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column40 : sparseSecondConjugationRoot5 40 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column41 : sparseSecondConjugationRoot5 41 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column42 : sparseSecondConjugationRoot5 42 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column43 : sparseSecondConjugationRoot5 43 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column44 : sparseSecondConjugationRoot5 44 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column45 : sparseSecondConjugationRoot5 45 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column46 : sparseSecondConjugationRoot5 46 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column47 : sparseSecondConjugationRoot5 47 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column48 : sparseSecondConjugationRoot5 48 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column49 : sparseSecondConjugationRoot5 49 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column50 : sparseSecondConjugationRoot5 50 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_column51 : sparseSecondConjugationRoot5 51 := by
  decide +kernel

private theorem sparse_second_conjugation_root5_all (j : Fin 52) : sparseSecondConjugationRoot5 j := by
  fin_cases j
  · exact sparse_second_conjugation_root5_column0
  · exact sparse_second_conjugation_root5_column1
  · exact sparse_second_conjugation_root5_column2
  · exact sparse_second_conjugation_root5_column3
  · exact sparse_second_conjugation_root5_column4
  · exact sparse_second_conjugation_root5_column5
  · exact sparse_second_conjugation_root5_column6
  · exact sparse_second_conjugation_root5_column7
  · exact sparse_second_conjugation_root5_column8
  · exact sparse_second_conjugation_root5_column9
  · exact sparse_second_conjugation_root5_column10
  · exact sparse_second_conjugation_root5_column11
  · exact sparse_second_conjugation_root5_column12
  · exact sparse_second_conjugation_root5_column13
  · exact sparse_second_conjugation_root5_column14
  · exact sparse_second_conjugation_root5_column15
  · exact sparse_second_conjugation_root5_column16
  · exact sparse_second_conjugation_root5_column17
  · exact sparse_second_conjugation_root5_column18
  · exact sparse_second_conjugation_root5_column19
  · exact sparse_second_conjugation_root5_column20
  · exact sparse_second_conjugation_root5_column21
  · exact sparse_second_conjugation_root5_column22
  · exact sparse_second_conjugation_root5_column23
  · exact sparse_second_conjugation_root5_column24
  · exact sparse_second_conjugation_root5_column25
  · exact sparse_second_conjugation_root5_column26
  · exact sparse_second_conjugation_root5_column27
  · exact sparse_second_conjugation_root5_column28
  · exact sparse_second_conjugation_root5_column29
  · exact sparse_second_conjugation_root5_column30
  · exact sparse_second_conjugation_root5_column31
  · exact sparse_second_conjugation_root5_column32
  · exact sparse_second_conjugation_root5_column33
  · exact sparse_second_conjugation_root5_column34
  · exact sparse_second_conjugation_root5_column35
  · exact sparse_second_conjugation_root5_column36
  · exact sparse_second_conjugation_root5_column37
  · exact sparse_second_conjugation_root5_column38
  · exact sparse_second_conjugation_root5_column39
  · exact sparse_second_conjugation_root5_column40
  · exact sparse_second_conjugation_root5_column41
  · exact sparse_second_conjugation_root5_column42
  · exact sparse_second_conjugation_root5_column43
  · exact sparse_second_conjugation_root5_column44
  · exact sparse_second_conjugation_root5_column45
  · exact sparse_second_conjugation_root5_column46
  · exact sparse_second_conjugation_root5_column47
  · exact sparse_second_conjugation_root5_column48
  · exact sparse_second_conjugation_root5_column49
  · exact sparse_second_conjugation_root5_column50
  · exact sparse_second_conjugation_root5_column51

theorem simple_commutator_5 : ∀ j : Fin 52,
    simpleMatrix 5 * basisMatrix j - basisMatrix j * simpleMatrix 5 =
      basisCombination (fun k => geckMatrix 5 k j) := by
  intro j
  rw [← denote_geckEntries 5, basisCombination_denote_column]
  simp only [← denote_simpleEntries 5, ← denote_basisEntries j,
    ← denote_product, ← denote_subEntries]
  exact sparse_commutator_root5_all j

theorem simple_second_conjugation_5 : ∀ j : Fin 52,
    simpleSecondMatrix 5 * basisMatrix j + basisMatrix j * simpleSecondMatrix 5 -
      simpleMatrix 5 * basisMatrix j * simpleMatrix 5 =
        basisCombination (fun k => geckSecondMatrix 5 k j) := by
  intro j
  rw [← denote_geckSecondEntries 5, basisCombination_denote_column]
  simp only [← denote_simpleEntries 5, ← denote_simpleSecondEntries 5,
    ← denote_basisEntries j, ← denote_product, ← denote_append,
    ← denote_subEntries]
  exact sparse_second_conjugation_root5_all j

theorem simple_third_conjugation_5 : ∀ j : Fin 52,
    simpleMatrix 5 * basisMatrix j * simpleSecondMatrix 5 -
      simpleSecondMatrix 5 * basisMatrix j * simpleMatrix 5 = 0 := by
  intro j
  simp only [← denote_simpleEntries 5, ← denote_simpleSecondEntries 5, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

theorem simple_fourth_conjugation_5 : ∀ j : Fin 52,
    simpleSecondMatrix 5 * basisMatrix j * simpleSecondMatrix 5 = 0 := by
  intro j
  simp only [← denote_simpleSecondEntries 5, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

end Atlas.Chevalley.Comparison.F4
