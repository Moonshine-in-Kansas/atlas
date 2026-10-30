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

theorem simple_square_2 :
    simpleMatrix 2 * simpleMatrix 2 = 2 • simpleSecondMatrix 2 := by
  simp only [← denote_simpleEntries 2, ← denote_simpleSecondEntries 2]
  simp only [← denote_product]
  decide +kernel

theorem simple_cube_2 :
    simpleSecondMatrix 2 * simpleMatrix 2 = 0 := by
  simp only [← denote_simpleEntries 2, ← denote_simpleSecondEntries 2]
  simp only [← denote_product]
  decide +kernel

theorem geck_square_2 :
    geckMatrix 2 * geckMatrix 2 = 2 • geckSecondMatrix 2 := by
  simp only [← denote_geckEntries 2, ← denote_geckSecondEntries 2]
  simp only [← denote_product]
  decide +kernel

theorem geck_cube_2 :
    geckSecondMatrix 2 * geckMatrix 2 = 0 := by
  simp only [← denote_geckEntries 2, ← denote_geckSecondEntries 2]
  simp only [← denote_product]
  decide +kernel

/-- Sparse propositions isolate individual column reductions. They use the
existing lists and introduce no new matrix or coefficient table. -/
private abbrev sparseCommutatorRoot2 (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleEntries 2) (basisEntries j))
    (product (basisEntries j) (simpleEntries 2))) =
      denote (columnEntries basisEntries (geckEntries 2) j)

private abbrev sparseSecondConjugationRoot2 (j : Fin 52) : Prop :=
  denote (subEntries
    (product (simpleSecondEntries 2) (basisEntries j) ++
      product (basisEntries j) (simpleSecondEntries 2))
    (product (product (simpleEntries 2) (basisEntries j)) (simpleEntries 2))) =
      denote (columnEntries basisEntries (geckSecondEntries 2) j)

private theorem sparse_commutator_root2_column0 : sparseCommutatorRoot2 0 := by
  decide +kernel

private theorem sparse_commutator_root2_column1 : sparseCommutatorRoot2 1 := by
  decide +kernel

private theorem sparse_commutator_root2_column2 : sparseCommutatorRoot2 2 := by
  decide +kernel

private theorem sparse_commutator_root2_column3 : sparseCommutatorRoot2 3 := by
  decide +kernel

private theorem sparse_commutator_root2_column4 : sparseCommutatorRoot2 4 := by
  decide +kernel

private theorem sparse_commutator_root2_column5 : sparseCommutatorRoot2 5 := by
  decide +kernel

private theorem sparse_commutator_root2_column6 : sparseCommutatorRoot2 6 := by
  decide +kernel

private theorem sparse_commutator_root2_column7 : sparseCommutatorRoot2 7 := by
  decide +kernel

private theorem sparse_commutator_root2_column8 : sparseCommutatorRoot2 8 := by
  decide +kernel

private theorem sparse_commutator_root2_column9 : sparseCommutatorRoot2 9 := by
  decide +kernel

private theorem sparse_commutator_root2_column10 : sparseCommutatorRoot2 10 := by
  decide +kernel

private theorem sparse_commutator_root2_column11 : sparseCommutatorRoot2 11 := by
  decide +kernel

private theorem sparse_commutator_root2_column12 : sparseCommutatorRoot2 12 := by
  decide +kernel

private theorem sparse_commutator_root2_column13 : sparseCommutatorRoot2 13 := by
  decide +kernel

private theorem sparse_commutator_root2_column14 : sparseCommutatorRoot2 14 := by
  decide +kernel

private theorem sparse_commutator_root2_column15 : sparseCommutatorRoot2 15 := by
  decide +kernel

private theorem sparse_commutator_root2_column16 : sparseCommutatorRoot2 16 := by
  decide +kernel

private theorem sparse_commutator_root2_column17 : sparseCommutatorRoot2 17 := by
  decide +kernel

private theorem sparse_commutator_root2_column18 : sparseCommutatorRoot2 18 := by
  decide +kernel

private theorem sparse_commutator_root2_column19 : sparseCommutatorRoot2 19 := by
  decide +kernel

private theorem sparse_commutator_root2_column20 : sparseCommutatorRoot2 20 := by
  decide +kernel

private theorem sparse_commutator_root2_column21 : sparseCommutatorRoot2 21 := by
  decide +kernel

private theorem sparse_commutator_root2_column22 : sparseCommutatorRoot2 22 := by
  decide +kernel

private theorem sparse_commutator_root2_column23 : sparseCommutatorRoot2 23 := by
  decide +kernel

private theorem sparse_commutator_root2_column24 : sparseCommutatorRoot2 24 := by
  decide +kernel

private theorem sparse_commutator_root2_column25 : sparseCommutatorRoot2 25 := by
  decide +kernel

private theorem sparse_commutator_root2_column26 : sparseCommutatorRoot2 26 := by
  decide +kernel

private theorem sparse_commutator_root2_column27 : sparseCommutatorRoot2 27 := by
  decide +kernel

private theorem sparse_commutator_root2_column28 : sparseCommutatorRoot2 28 := by
  decide +kernel

private theorem sparse_commutator_root2_column29 : sparseCommutatorRoot2 29 := by
  decide +kernel

private theorem sparse_commutator_root2_column30 : sparseCommutatorRoot2 30 := by
  decide +kernel

private theorem sparse_commutator_root2_column31 : sparseCommutatorRoot2 31 := by
  decide +kernel

private theorem sparse_commutator_root2_column32 : sparseCommutatorRoot2 32 := by
  decide +kernel

private theorem sparse_commutator_root2_column33 : sparseCommutatorRoot2 33 := by
  decide +kernel

private theorem sparse_commutator_root2_column34 : sparseCommutatorRoot2 34 := by
  decide +kernel

private theorem sparse_commutator_root2_column35 : sparseCommutatorRoot2 35 := by
  decide +kernel

private theorem sparse_commutator_root2_column36 : sparseCommutatorRoot2 36 := by
  decide +kernel

private theorem sparse_commutator_root2_column37 : sparseCommutatorRoot2 37 := by
  decide +kernel

private theorem sparse_commutator_root2_column38 : sparseCommutatorRoot2 38 := by
  decide +kernel

private theorem sparse_commutator_root2_column39 : sparseCommutatorRoot2 39 := by
  decide +kernel

private theorem sparse_commutator_root2_column40 : sparseCommutatorRoot2 40 := by
  decide +kernel

private theorem sparse_commutator_root2_column41 : sparseCommutatorRoot2 41 := by
  decide +kernel

private theorem sparse_commutator_root2_column42 : sparseCommutatorRoot2 42 := by
  decide +kernel

private theorem sparse_commutator_root2_column43 : sparseCommutatorRoot2 43 := by
  decide +kernel

private theorem sparse_commutator_root2_column44 : sparseCommutatorRoot2 44 := by
  decide +kernel

private theorem sparse_commutator_root2_column45 : sparseCommutatorRoot2 45 := by
  decide +kernel

private theorem sparse_commutator_root2_column46 : sparseCommutatorRoot2 46 := by
  decide +kernel

private theorem sparse_commutator_root2_column47 : sparseCommutatorRoot2 47 := by
  decide +kernel

private theorem sparse_commutator_root2_column48 : sparseCommutatorRoot2 48 := by
  decide +kernel

private theorem sparse_commutator_root2_column49 : sparseCommutatorRoot2 49 := by
  decide +kernel

private theorem sparse_commutator_root2_column50 : sparseCommutatorRoot2 50 := by
  decide +kernel

private theorem sparse_commutator_root2_column51 : sparseCommutatorRoot2 51 := by
  decide +kernel

private theorem sparse_commutator_root2_all (j : Fin 52) : sparseCommutatorRoot2 j := by
  fin_cases j
  · exact sparse_commutator_root2_column0
  · exact sparse_commutator_root2_column1
  · exact sparse_commutator_root2_column2
  · exact sparse_commutator_root2_column3
  · exact sparse_commutator_root2_column4
  · exact sparse_commutator_root2_column5
  · exact sparse_commutator_root2_column6
  · exact sparse_commutator_root2_column7
  · exact sparse_commutator_root2_column8
  · exact sparse_commutator_root2_column9
  · exact sparse_commutator_root2_column10
  · exact sparse_commutator_root2_column11
  · exact sparse_commutator_root2_column12
  · exact sparse_commutator_root2_column13
  · exact sparse_commutator_root2_column14
  · exact sparse_commutator_root2_column15
  · exact sparse_commutator_root2_column16
  · exact sparse_commutator_root2_column17
  · exact sparse_commutator_root2_column18
  · exact sparse_commutator_root2_column19
  · exact sparse_commutator_root2_column20
  · exact sparse_commutator_root2_column21
  · exact sparse_commutator_root2_column22
  · exact sparse_commutator_root2_column23
  · exact sparse_commutator_root2_column24
  · exact sparse_commutator_root2_column25
  · exact sparse_commutator_root2_column26
  · exact sparse_commutator_root2_column27
  · exact sparse_commutator_root2_column28
  · exact sparse_commutator_root2_column29
  · exact sparse_commutator_root2_column30
  · exact sparse_commutator_root2_column31
  · exact sparse_commutator_root2_column32
  · exact sparse_commutator_root2_column33
  · exact sparse_commutator_root2_column34
  · exact sparse_commutator_root2_column35
  · exact sparse_commutator_root2_column36
  · exact sparse_commutator_root2_column37
  · exact sparse_commutator_root2_column38
  · exact sparse_commutator_root2_column39
  · exact sparse_commutator_root2_column40
  · exact sparse_commutator_root2_column41
  · exact sparse_commutator_root2_column42
  · exact sparse_commutator_root2_column43
  · exact sparse_commutator_root2_column44
  · exact sparse_commutator_root2_column45
  · exact sparse_commutator_root2_column46
  · exact sparse_commutator_root2_column47
  · exact sparse_commutator_root2_column48
  · exact sparse_commutator_root2_column49
  · exact sparse_commutator_root2_column50
  · exact sparse_commutator_root2_column51

private theorem sparse_second_conjugation_root2_column0 : sparseSecondConjugationRoot2 0 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column1 : sparseSecondConjugationRoot2 1 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column2 : sparseSecondConjugationRoot2 2 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column3 : sparseSecondConjugationRoot2 3 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column4 : sparseSecondConjugationRoot2 4 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column5 : sparseSecondConjugationRoot2 5 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column6 : sparseSecondConjugationRoot2 6 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column7 : sparseSecondConjugationRoot2 7 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column8 : sparseSecondConjugationRoot2 8 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column9 : sparseSecondConjugationRoot2 9 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column10 : sparseSecondConjugationRoot2 10 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column11 : sparseSecondConjugationRoot2 11 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column12 : sparseSecondConjugationRoot2 12 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column13 : sparseSecondConjugationRoot2 13 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column14 : sparseSecondConjugationRoot2 14 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column15 : sparseSecondConjugationRoot2 15 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column16 : sparseSecondConjugationRoot2 16 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column17 : sparseSecondConjugationRoot2 17 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column18 : sparseSecondConjugationRoot2 18 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column19 : sparseSecondConjugationRoot2 19 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column20 : sparseSecondConjugationRoot2 20 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column21 : sparseSecondConjugationRoot2 21 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column22 : sparseSecondConjugationRoot2 22 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column23 : sparseSecondConjugationRoot2 23 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column24 : sparseSecondConjugationRoot2 24 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column25 : sparseSecondConjugationRoot2 25 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column26 : sparseSecondConjugationRoot2 26 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column27 : sparseSecondConjugationRoot2 27 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column28 : sparseSecondConjugationRoot2 28 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column29 : sparseSecondConjugationRoot2 29 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column30 : sparseSecondConjugationRoot2 30 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column31 : sparseSecondConjugationRoot2 31 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column32 : sparseSecondConjugationRoot2 32 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column33 : sparseSecondConjugationRoot2 33 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column34 : sparseSecondConjugationRoot2 34 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column35 : sparseSecondConjugationRoot2 35 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column36 : sparseSecondConjugationRoot2 36 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column37 : sparseSecondConjugationRoot2 37 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column38 : sparseSecondConjugationRoot2 38 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column39 : sparseSecondConjugationRoot2 39 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column40 : sparseSecondConjugationRoot2 40 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column41 : sparseSecondConjugationRoot2 41 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column42 : sparseSecondConjugationRoot2 42 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column43 : sparseSecondConjugationRoot2 43 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column44 : sparseSecondConjugationRoot2 44 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column45 : sparseSecondConjugationRoot2 45 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column46 : sparseSecondConjugationRoot2 46 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column47 : sparseSecondConjugationRoot2 47 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column48 : sparseSecondConjugationRoot2 48 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column49 : sparseSecondConjugationRoot2 49 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column50 : sparseSecondConjugationRoot2 50 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_column51 : sparseSecondConjugationRoot2 51 := by
  decide +kernel

private theorem sparse_second_conjugation_root2_all (j : Fin 52) : sparseSecondConjugationRoot2 j := by
  fin_cases j
  · exact sparse_second_conjugation_root2_column0
  · exact sparse_second_conjugation_root2_column1
  · exact sparse_second_conjugation_root2_column2
  · exact sparse_second_conjugation_root2_column3
  · exact sparse_second_conjugation_root2_column4
  · exact sparse_second_conjugation_root2_column5
  · exact sparse_second_conjugation_root2_column6
  · exact sparse_second_conjugation_root2_column7
  · exact sparse_second_conjugation_root2_column8
  · exact sparse_second_conjugation_root2_column9
  · exact sparse_second_conjugation_root2_column10
  · exact sparse_second_conjugation_root2_column11
  · exact sparse_second_conjugation_root2_column12
  · exact sparse_second_conjugation_root2_column13
  · exact sparse_second_conjugation_root2_column14
  · exact sparse_second_conjugation_root2_column15
  · exact sparse_second_conjugation_root2_column16
  · exact sparse_second_conjugation_root2_column17
  · exact sparse_second_conjugation_root2_column18
  · exact sparse_second_conjugation_root2_column19
  · exact sparse_second_conjugation_root2_column20
  · exact sparse_second_conjugation_root2_column21
  · exact sparse_second_conjugation_root2_column22
  · exact sparse_second_conjugation_root2_column23
  · exact sparse_second_conjugation_root2_column24
  · exact sparse_second_conjugation_root2_column25
  · exact sparse_second_conjugation_root2_column26
  · exact sparse_second_conjugation_root2_column27
  · exact sparse_second_conjugation_root2_column28
  · exact sparse_second_conjugation_root2_column29
  · exact sparse_second_conjugation_root2_column30
  · exact sparse_second_conjugation_root2_column31
  · exact sparse_second_conjugation_root2_column32
  · exact sparse_second_conjugation_root2_column33
  · exact sparse_second_conjugation_root2_column34
  · exact sparse_second_conjugation_root2_column35
  · exact sparse_second_conjugation_root2_column36
  · exact sparse_second_conjugation_root2_column37
  · exact sparse_second_conjugation_root2_column38
  · exact sparse_second_conjugation_root2_column39
  · exact sparse_second_conjugation_root2_column40
  · exact sparse_second_conjugation_root2_column41
  · exact sparse_second_conjugation_root2_column42
  · exact sparse_second_conjugation_root2_column43
  · exact sparse_second_conjugation_root2_column44
  · exact sparse_second_conjugation_root2_column45
  · exact sparse_second_conjugation_root2_column46
  · exact sparse_second_conjugation_root2_column47
  · exact sparse_second_conjugation_root2_column48
  · exact sparse_second_conjugation_root2_column49
  · exact sparse_second_conjugation_root2_column50
  · exact sparse_second_conjugation_root2_column51

theorem simple_commutator_2 : ∀ j : Fin 52,
    simpleMatrix 2 * basisMatrix j - basisMatrix j * simpleMatrix 2 =
      basisCombination (fun k => geckMatrix 2 k j) := by
  intro j
  rw [← denote_geckEntries 2, basisCombination_denote_column]
  simp only [← denote_simpleEntries 2, ← denote_basisEntries j,
    ← denote_product, ← denote_subEntries]
  exact sparse_commutator_root2_all j

theorem simple_second_conjugation_2 : ∀ j : Fin 52,
    simpleSecondMatrix 2 * basisMatrix j + basisMatrix j * simpleSecondMatrix 2 -
      simpleMatrix 2 * basisMatrix j * simpleMatrix 2 =
        basisCombination (fun k => geckSecondMatrix 2 k j) := by
  intro j
  rw [← denote_geckSecondEntries 2, basisCombination_denote_column]
  simp only [← denote_simpleEntries 2, ← denote_simpleSecondEntries 2,
    ← denote_basisEntries j, ← denote_product, ← denote_append,
    ← denote_subEntries]
  exact sparse_second_conjugation_root2_all j

theorem simple_third_conjugation_2 : ∀ j : Fin 52,
    simpleMatrix 2 * basisMatrix j * simpleSecondMatrix 2 -
      simpleSecondMatrix 2 * basisMatrix j * simpleMatrix 2 = 0 := by
  intro j
  simp only [← denote_simpleEntries 2, ← denote_simpleSecondEntries 2, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

theorem simple_fourth_conjugation_2 : ∀ j : Fin 52,
    simpleSecondMatrix 2 * basisMatrix j * simpleSecondMatrix 2 = 0 := by
  intro j
  simp only [← denote_simpleSecondEntries 2, ← denote_basisEntries j]
  simp only [← denote_product]
  fin_cases j <;> decide +kernel

end Atlas.Chevalley.Comparison.F4
