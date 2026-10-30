import Atlas.LinearGroups.Chevalley.Comparison.F4.GeckOperatorsBase

noncomputable section
namespace Atlas.Chevalley.Comparison.F4
open Classical Integral F4Data
open scoped Matrix
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem E_numeric_table_root0_row0 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (0 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (0 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row1 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (1 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (1 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row2 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (2 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (2 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row3 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (3 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (3 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row4 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (4 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (4 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row5 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (5 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (5 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row6 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (6 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (6 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row7 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (7 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (7 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row8 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (8 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (8 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row9 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (9 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (9 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row10 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (10 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (10 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row11 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (11 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (11 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row12 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (12 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (12 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row13 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (13 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (13 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row14 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (14 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (14 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row15 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (15 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (15 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row16 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (16 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (16 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row17 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (17 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (17 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row18 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (18 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (18 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row19 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (19 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (19 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row20 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (20 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (20 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row21 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (21 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (21 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row22 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (22 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (22 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row23 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (23 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (23 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row24 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (24 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (24 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row25 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (25 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (25 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row26 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (26 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (26 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row27 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (27 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (27 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row28 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (28 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (28 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row29 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (29 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (29 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row30 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (30 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (30 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row31 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (31 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (31 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row32 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (32 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (32 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row33 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (33 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (33 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row34 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (34 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (34 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row35 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (35 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (35 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row36 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (36 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (36 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row37 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (37 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (37 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row38 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (38 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (38 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row39 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (39 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (39 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row40 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (40 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (40 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row41 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (41 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (41 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row42 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (42 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (42 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row43 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (43 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (43 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row44 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (44 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (44 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row45 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (45 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (45 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row46 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (46 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (46 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row47 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (47 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (47 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row48 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (48 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (48 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row49 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (49 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (49 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row50 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (50 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (50 : Fin 52) c := by
  decide +kernel

private theorem E_numeric_table_root0_row51 : ∀ c : Fin 52,
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm (51 : Fin 52))
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) (51 : Fin 52) c := by
  decide +kernel

theorem E_numeric_table_root0 : ∀ (a c : Fin 52),
    E (0 : Fin 4) ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm a)
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 (0 : Fin 4)) a c := by
  intro a c
  fin_cases a
  · exact E_numeric_table_root0_row0 c
  · exact E_numeric_table_root0_row1 c
  · exact E_numeric_table_root0_row2 c
  · exact E_numeric_table_root0_row3 c
  · exact E_numeric_table_root0_row4 c
  · exact E_numeric_table_root0_row5 c
  · exact E_numeric_table_root0_row6 c
  · exact E_numeric_table_root0_row7 c
  · exact E_numeric_table_root0_row8 c
  · exact E_numeric_table_root0_row9 c
  · exact E_numeric_table_root0_row10 c
  · exact E_numeric_table_root0_row11 c
  · exact E_numeric_table_root0_row12 c
  · exact E_numeric_table_root0_row13 c
  · exact E_numeric_table_root0_row14 c
  · exact E_numeric_table_root0_row15 c
  · exact E_numeric_table_root0_row16 c
  · exact E_numeric_table_root0_row17 c
  · exact E_numeric_table_root0_row18 c
  · exact E_numeric_table_root0_row19 c
  · exact E_numeric_table_root0_row20 c
  · exact E_numeric_table_root0_row21 c
  · exact E_numeric_table_root0_row22 c
  · exact E_numeric_table_root0_row23 c
  · exact E_numeric_table_root0_row24 c
  · exact E_numeric_table_root0_row25 c
  · exact E_numeric_table_root0_row26 c
  · exact E_numeric_table_root0_row27 c
  · exact E_numeric_table_root0_row28 c
  · exact E_numeric_table_root0_row29 c
  · exact E_numeric_table_root0_row30 c
  · exact E_numeric_table_root0_row31 c
  · exact E_numeric_table_root0_row32 c
  · exact E_numeric_table_root0_row33 c
  · exact E_numeric_table_root0_row34 c
  · exact E_numeric_table_root0_row35 c
  · exact E_numeric_table_root0_row36 c
  · exact E_numeric_table_root0_row37 c
  · exact E_numeric_table_root0_row38 c
  · exact E_numeric_table_root0_row39 c
  · exact E_numeric_table_root0_row40 c
  · exact E_numeric_table_root0_row41 c
  · exact E_numeric_table_root0_row42 c
  · exact E_numeric_table_root0_row43 c
  · exact E_numeric_table_root0_row44 c
  · exact E_numeric_table_root0_row45 c
  · exact E_numeric_table_root0_row46 c
  · exact E_numeric_table_root0_row47 c
  · exact E_numeric_table_root0_row48 c
  · exact E_numeric_table_root0_row49 c
  · exact E_numeric_table_root0_row50 c
  · exact E_numeric_table_root0_row51 c

end Atlas.Chevalley.Comparison.F4
