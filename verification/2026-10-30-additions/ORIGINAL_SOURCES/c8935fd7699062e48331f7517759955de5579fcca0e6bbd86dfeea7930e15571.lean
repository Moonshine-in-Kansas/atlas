import F4Work.F4IntegralSparseData
import F4Work.F4SparseBasisCombination

/-! Literal integral identities. No finite-field or group-order certificate. -/
namespace Atlas.Chevalley.Comparison.F4
open scoped Matrix
open Atlas.LinearAlgebra.SparseIntegralMatrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem simple_square_6 :
    simpleMatrix 6 * simpleMatrix 6 = 2 • simpleSecondMatrix 6 := by
  simp only [← denote_simpleEntries 6, ← denote_simpleSecondEntries 6]
  simp only [← denote_product]
  decide +kernel

theorem simple_cube_6 :
    simpleSecondMatrix 6 * simpleMatrix 6 = 0 := by
  simp only [← denote_simpleEntries 6, ← denote_simpleSecondEntries 6]
  simp only [← denote_product]
  decide +kernel

theorem geck_square_6 :
    geckMatrix 6 * geckMatrix 6 = 2 • geckSecondMatrix 6 := by
  simp only [← denote_geckEntries 6, ← denote_geckSecondEntries 6]
  simp only [← denote_product]
  decide +kernel

theorem geck_cube_6 :
    geckSecondMatrix 6 * geckMatrix 6 = 0 := by
  simp only [← denote_geckEntries 6, ← denote_geckSecondEntries 6]
  simp only [← denote_product]
  decide +kernel

/-- Sparse propositions isolate individual column reductions. They use the
existing lists and introduce no new matrix or coefficient table. -/
private abbrev sparseCommutatorRoot6 (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleEntries 6) (basisEntries j))
    (product (basisEntries j) (simpleEntries 6))) =
      denote (columnEntries basisEntries (geckEntries 6) j)

private abbrev sparseSecondConjugationRoot6 (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleSecondEntries 6) (basisEntries j) ++
      product (basisEntries j) (simpleSecondEntries 6))
    (product (product (simpleEntries 6) (basisEntries j)) (simpleEntries 6))) =
      denote (columnEntries basisEntries (geckSecondEntries 6) j)

private theorem sparse_commutator_root6_column0 : sparseCommutatorRoot6 0 := by
  decide +kernel

private theorem sparse_commutator_root6_column1 : sparseCommutatorRoot6 1 := by
  decide +kernel

private theorem sparse_commutator_root6_column2 : sparseCommutatorRoot6 2 := by
  decide +kernel

private theorem sparse_commutator_root6_column3 : sparseCommutatorRoot6 3 := by
  decide +kernel

private theorem sparse_commutator_root6_column4 : sparseCommutatorRoot6 4 := by
  decide +kernel

private theorem sparse_commutator_root6_column5 : sparseCommutatorRoot6 5 := by
  decide +kernel

private theorem sparse_commutator_root6_column6 : sparseCommutatorRoot6 6 := by
  decide +kernel

private theorem sparse_commutator_root6_column7 : sparseCommutatorRoot6 7 := by
  decide +kernel

private theorem sparse_commutator_root6_column8 : sparseCommutatorRoot6 8 := by
  decide +kernel

private theorem sparse_commutator_root6_column9 : sparseCommutatorRoot6 9 := by
  decide +kernel

private theorem sparse_commutator_root6_column10 : sparseCommutatorRoot6 10 := by
  decide +kernel

private theorem sparse_commutator_root6_column11 : sparseCommutatorRoot6 11 := by
  decide +kernel

private theorem sparse_commutator_root6_column12 : sparseCommutatorRoot6 12 := by
  decide +kernel

private theorem sparse_commutator_root6_column13 : sparseCommutatorRoot6 13 := by
  decide +kernel

private theorem sparse_commutator_root6_column14 : sparseCommutatorRoot6 14 := by
  decide +kernel

private theorem sparse_commutator_root6_column15 : sparseCommutatorRoot6 15 := by
  decide +kernel

private theorem sparse_commutator_root6_column16 : sparseCommutatorRoot6 16 := by
  decide +kernel

private theorem sparse_commutator_root6_column17 : sparseCommutatorRoot6 17 := by
  decide +kernel

private theorem sparse_commutator_root6_column18 : sparseCommutatorRoot6 18 := by
  decide +kernel

private theorem sparse_commutator_root6_column19 : sparseCommutatorRoot6 19 := by
  decide +kernel

private theorem sparse_commutator_root6_column20 : sparseCommutatorRoot6 20 := by
  decide +kernel

private theorem sparse_commutator_root6_column21 : sparseCommutatorRoot6 21 := by
  decide +kernel

private theorem sparse_commutator_root6_column22 : sparseCommutatorRoot6 22 := by
  decide +kernel

private theorem sparse_commutator_root6_column23 : sparseCommutatorRoot6 23 := by
  decide +kernel

private theorem sparse_commutator_root6_column24 : sparseCommutatorRoot6 24 := by
  decide +kernel

private theorem sparse_commutator_root6_column25 : sparseCommutatorRoot6 25 := by
  decide +kernel

private theorem sparse_commutator_root6_column26 : sparseCommutatorRoot6 26 := by
  decide +kernel

private theorem sparse_commutator_root6_column27 : sparseCommutatorRoot6 27 := by
  decide +kernel

private theorem sparse_commutator_root6_column28 : sparseCommutatorRoot6 28 := by
  decide +kernel

private theorem sparse_commutator_root6_column29 : sparseCommutatorRoot6 29 := by
  decide +kernel

private theorem sparse_commutator_root6_column30 : sparseCommutatorRoot6 30 := by
  decide +kernel

private theorem sparse_commutator_root6_column31 : sparseCommutatorRoot6 31 := by
  decide +kernel

private theorem sparse_commutator_root6_column32 : sparseCommutatorRoot6 32 := by
  decide +kernel

private theorem sparse_commutator_root6_column33 : sparseCommutatorRoot6 33 := by
  decide +kernel

private theorem sparse_commutator_root6_column34 : sparseCommutatorRoot6 34 := by
  decide +kernel

private theorem sparse_commutator_root6_column35 : sparseCommutatorRoot6 35 := by
  decide +kernel

private theorem sparse_commutator_root6_column36 : sparseCommutatorRoot6 36 := by
  decide +kernel

private theorem sparse_commutator_root6_column37 : sparseCommutatorRoot6 37 := by
  decide +kernel

private theorem sparse_commutator_root6_column38 : sparseCommutatorRoot6 38 := by
  decide +kernel

private theorem sparse_commutator_root6_column39 : sparseCommutatorRoot6 39 := by
  decide +kernel

private theorem sparse_commutator_root6_column40 : sparseCommutatorRoot6 40 := by
  decide +kernel

private theorem sparse_commutator_root6_column41 : sparseCommutatorRoot6 41 := by
  decide +kernel

private theorem sparse_commutator_root6_column42 : sparseCommutatorRoot6 42 := by
  decide +kernel

private theorem sparse_commutator_root6_column43 : sparseCommutatorRoot6 43 := by
  decide +kernel

private theorem sparse_commutator_root6_column44 : sparseCommutatorRoot6 44 := by
  decide +kernel

private theorem sparse_commutator_root6_column45 : sparseCommutatorRoot6 45 := by
  decide +kernel

private theorem sparse_commutator_root6_column46 : sparseCommutatorRoot6 46 := by
  decide +kernel

private theorem sparse_commutator_root6_column47 : sparseCommutatorRoot6 47 := by
  decide +kernel

private theorem sparse_commutator_root6_column48 : sparseCommutatorRoot6 48 := by
  decide +kernel

private theorem sparse_commutator_root6_column49 : sparseCommutatorRoot6 49 := by
  decide +kernel

private theorem sparse_commutator_root6_column50 : sparseCommutatorRoot6 50 := by
  decide +kernel

private theorem sparse_commutator_root6_column51 : sparseCommutatorRoot6 51 := by
  decide +kernel

private theorem sparse_commutator_root6_all (j : Fin 52) : sparseCommutatorRoot6 j := by
  fin_cases j
  · exact sparse_commutator_root6_column0
  · exact sparse_commutator_root6_column1
  · exact sparse_commutator_root6_column2
  · exact sparse_commutator_root6_column3
  · exact sparse_commutator_root6_column4
  · exact sparse_commutator_root6_column5
  · exact sparse_commutator_root6_column6
  · exact sparse_commutator_root6_column7
  · exact sparse_commutator_root6_column8
  · exact sparse_commutator_root6_column9
  · exact sparse_commutator_root6_column10
  · exact sparse_commutator_root6_column11
  · exact sparse_commutator_root6_column12
  · exact sparse_commutator_root6_column13
  · exact sparse_commutator_root6_column14
  · exact sparse_commutator_root6_column15
  · exact sparse_commutator_root6_column16
  · exact sparse_commutator_root6_column17
  · exact sparse_commutator_root6_column18
  · exact sparse_commutator_root6_column19
  · exact sparse_commutator_root6_column20
  · exact sparse_commutator_root6_column21
  · exact sparse_commutator_root6_column22
  · exact sparse_commutator_root6_column23
  · exact sparse_commutator_root6_column24
  · exact sparse_commutator_root6_column25
  · exact sparse_commutator_root6_column26
  · exact sparse_commutator_root6_column27
  · exact sparse_commutator_root6_column28
  · exact sparse_commutator_root6_column29
  · exact sparse_commutator_root6_column30
  · exact sparse_commutator_root6_column31
  · exact sparse_commutator_root6_column32
  · exact sparse_commutator_root6_column33
  · exact sparse_commutator_root6_column34
  · exact sparse_commutator_root6_column35
  · exact sparse_commutator_root6_column36
  · exact sparse_commutator_root6_column37
  · exact sparse_commutator_root6_column38
  · exact sparse_commutator_root6_column39
  · exact sparse_commutator_root6_column40
  · exact sparse_commutator_root6_column41
  · exact sparse_commutator_root6_column42
  · exact sparse_commutator_root6_column43
  · exact sparse_commutator_root6_column44
  · exact sparse_commutator_root6_column45
  · exact sparse_commutator_root6_column46
  · exact sparse_commutator_root6_column47
  · exact sparse_commutator_root6_column48
  · exact sparse_commutator_root6_column49
  · exact sparse_commutator_root6_column50
  · exact sparse_commutator_root6_column51

private theorem sparse_second_conjugation_root6_column0 : sparseSecondConjugationRoot6 0 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column1 : sparseSecondConjugationRoot6 1 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column2 : sparseSecondConjugationRoot6 2 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column3 : sparseSecondConjugationRoot6 3 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column4 : sparseSecondConjugationRoot6 4 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column5 : sparseSecondConjugationRoot6 5 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column6 : sparseSecondConjugationRoot6 6 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column7 : sparseSecondConjugationRoot6 7 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column8 : sparseSecondConjugationRoot6 8 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column9 : sparseSecondConjugationRoot6 9 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column10 : sparseSecondConjugationRoot6 10 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column11 : sparseSecondConjugationRoot6 11 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column12 : sparseSecondConjugationRoot6 12 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column13 : sparseSecondConjugationRoot6 13 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column14 : sparseSecondConjugationRoot6 14 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column15 : sparseSecondConjugationRoot6 15 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column16 : sparseSecondConjugationRoot6 16 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column17 : sparseSecondConjugationRoot6 17 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column18 : sparseSecondConjugationRoot6 18 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column19 : sparseSecondConjugationRoot6 19 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column20 : sparseSecondConjugationRoot6 20 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column21 : sparseSecondConjugationRoot6 21 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column22 : sparseSecondConjugationRoot6 22 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column23 : sparseSecondConjugationRoot6 23 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column24 : sparseSecondConjugationRoot6 24 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column25 : sparseSecondConjugationRoot6 25 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column26 : sparseSecondConjugationRoot6 26 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column27 : sparseSecondConjugationRoot6 27 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column28 : sparseSecondConjugationRoot6 28 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column29 : sparseSecondConjugationRoot6 29 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column30 : sparseSecondConjugationRoot6 30 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column31 : sparseSecondConjugationRoot6 31 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column32 : sparseSecondConjugationRoot6 32 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column33 : sparseSecondConjugationRoot6 33 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column34 : sparseSecondConjugationRoot6 34 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column35 : sparseSecondConjugationRoot6 35 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column36 : sparseSecondConjugationRoot6 36 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column37 : sparseSecondConjugationRoot6 37 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column38 : sparseSecondConjugationRoot6 38 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column39 : sparseSecondConjugationRoot6 39 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column40 : sparseSecondConjugationRoot6 40 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column41 : sparseSecondConjugationRoot6 41 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column42 : sparseSecondConjugationRoot6 42 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column43 : sparseSecondConjugationRoot6 43 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column44 : sparseSecondConjugationRoot6 44 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column45 : sparseSecondConjugationRoot6 45 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column46 : sparseSecondConjugationRoot6 46 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column47 : sparseSecondConjugationRoot6 47 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column48 : sparseSecondConjugationRoot6 48 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column49 : sparseSecondConjugationRoot6 49 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column50 : sparseSecondConjugationRoot6 50 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_column51 : sparseSecondConjugationRoot6 51 := by
  decide +kernel

private theorem sparse_second_conjugation_root6_all (j : Fin 52) : sparseSecondConjugationRoot6 j := by
  fin_cases j
  · exact sparse_second_conjugation_root6_column0
  · exact sparse_second_conjugation_root6_column1
  · exact sparse_second_conjugation_root6_column2
  · exact sparse_second_conjugation_root6_column3
  · exact sparse_second_conjugation_root6_column4
  · exact sparse_second_conjugation_root6_column5
  · exact sparse_second_conjugation_root6_column6
  · exact sparse_second_conjugation_root6_column7
  · exact sparse_second_conjugation_root6_column8
  · exact sparse_second_conjugation_root6_column9
  · exact sparse_second_conjugation_root6_column10
  · exact sparse_second_conjugation_root6_column11
  · exact sparse_second_conjugation_root6_column12
  · exact sparse_second_conjugation_root6_column13
  · exact sparse_second_conjugation_root6_column14
  · exact sparse_second_conjugation_root6_column15
  · exact sparse_second_conjugation_root6_column16
  · exact sparse_second_conjugation_root6_column17
  · exact sparse_second_conjugation_root6_column18
  · exact sparse_second_conjugation_root6_column19
  · exact sparse_second_conjugation_root6_column20
  · exact sparse_second_conjugation_root6_column21
  · exact sparse_second_conjugation_root6_column22
  · exact sparse_second_conjugation_root6_column23
  · exact sparse_second_conjugation_root6_column24
  · exact sparse_second_conjugation_root6_column25
  · exact sparse_second_conjugation_root6_column26
  · exact sparse_second_conjugation_root6_column27
  · exact sparse_second_conjugation_root6_column28
  · exact sparse_second_conjugation_root6_column29
  · exact sparse_second_conjugation_root6_column30
  · exact sparse_second_conjugation_root6_column31
  · exact sparse_second_conjugation_root6_column32
  · exact sparse_second_conjugation_root6_column33
  · exact sparse_second_conjugation_root6_column34
  · exact sparse_second_conjugation_root6_column35
  · exact sparse_second_conjugation_root6_column36
  · exact sparse_second_conjugation_root6_column37
  · exact sparse_second_conjugation_root6_column38
  · exact sparse_second_conjugation_root6_column39
  · exact sparse_second_conjugation_root6_column40
  · exact sparse_second_conjugation_root6_column41
  · exact sparse_second_conjugation_root6_column42
  · exact sparse_second_conjugation_root6_column43
  · exact sparse_second_conjugation_root6_column44
  · exact sparse_second_conjugation_root6_column45
  · exact sparse_second_conjugation_root6_column46
  · exact sparse_second_conjugation_root6_column47
  · exact sparse_second_conjugation_root6_column48
  · exact sparse_second_conjugation_root6_column49
  · exact sparse_second_conjugation_root6_column50
  · exact sparse_second_conjugation_root6_column51

theorem simple_commutator_6 : ∀ j : Fin 52,
    simpleMatrix 6 * basisMatrix j - basisMatrix j * simpleMatrix 6 =
      basisCombination (fun k => geckMatrix 6 k j) := by
  intro j
  rw [← denote_geckEntries 6, basisCombination_denote_column]
  simp only [← denote_simpleEntries 6, ← denote_basisEntries j,
    ← denote_product, ← denote_subEntries]
  exact sparse_commutator_root6_all j

theorem simple_second_conjugation_6 : ∀ j : Fin 52,
    simpleSecondMatrix 6 * basisMatrix j + basisMatrix j * simpleSecondMatrix 6 -
      simpleMatrix 6 * basisMatrix j * simpleMatrix 6 =
        basisCombination (fun k => geckSecondMatrix 6 k j) := by
  intro j
  rw [← denote_geckSecondEntries 6, basisCombination_denote_column]
  simp only [← denote_simpleEntries 6, ← denote_simpleSecondEntries 6,
    ← denote_basisEntries j, ← denote_product, ← denote_append,
    ← denote_subEntries]
  exact sparse_second_conjugation_root6_all j

theorem simple_third_conjugation_6 : ∀ j : Fin 52,
    simpleMatrix 6 * basisMatrix j * simpleSecondMatrix 6 -
      simpleSecondMatrix 6 * basisMatrix j * simpleMatrix 6 = 0 := by
  intro j
  simp only [← denote_simpleEntries 6, ← denote_simpleSecondEntries 6, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

theorem simple_fourth_conjugation_6 : ∀ j : Fin 52,
    simpleSecondMatrix 6 * basisMatrix j * simpleSecondMatrix 6 = 0 := by
  intro j
  simp only [← denote_simpleSecondEntries 6, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

end Atlas.Chevalley.Comparison.F4
