import Atlas.LinearGroups.Chevalley.Comparison.F4.GeckOppositionBase

noncomputable section
namespace Atlas.Chevalley.Comparison.F4
open Integral F4Data
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000


private theorem geck_negative_root3_row0 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (0 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (0 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row1 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (1 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (1 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row2 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (2 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (2 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row3 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (3 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (3 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row4 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (4 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (4 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row5 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (5 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (5 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row6 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (6 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (6 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row7 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (7 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (7 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row8 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (8 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (8 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row9 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (9 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (9 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row10 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (10 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (10 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row11 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (11 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (11 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row12 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (12 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (12 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row13 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (13 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (13 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row14 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (14 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (14 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row15 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (15 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (15 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row16 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (16 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (16 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row17 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (17 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (17 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row18 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (18 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (18 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row19 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (19 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (19 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row20 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (20 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (20 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row21 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (21 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (21 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row22 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (22 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (22 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row23 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (23 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (23 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row24 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (24 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (24 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row25 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (25 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (25 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row26 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (26 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (26 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row27 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (27 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (27 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row28 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (28 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (28 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row29 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (29 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (29 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row30 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (30 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (30 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row31 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (31 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (31 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row32 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (32 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (32 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row33 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (33 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (33 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row34 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (34 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (34 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row35 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (35 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (35 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row36 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (36 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (36 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row37 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (37 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (37 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row38 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (38 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (38 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row39 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (39 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (39 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row40 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (40 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (40 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row41 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (41 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (41 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row42 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (42 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (42 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row43 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (43 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (43 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row44 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (44 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (44 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row45 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (45 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (45 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row46 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (46 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (46 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row47 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (47 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (47 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row48 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (48 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (48 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row49 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (49 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (49 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row50 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (50 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (50 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

private theorem geck_negative_root3_row51 : ∀ c : Fin 52,
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) (51 : Fin 52) c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (51 : Fin 52))
        (opposite52 c) := by
  unfold geckMatrix opposite52
  decide +kernel

theorem geck_negative_root3 : ∀ (a c : Fin 52),
    geckMatrix (Fin.natAdd 4 (3 : Fin 4)) a c =
      geckMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 a) (opposite52 c) := by
  intro a c
  fin_cases a
  · exact geck_negative_root3_row0 c
  · exact geck_negative_root3_row1 c
  · exact geck_negative_root3_row2 c
  · exact geck_negative_root3_row3 c
  · exact geck_negative_root3_row4 c
  · exact geck_negative_root3_row5 c
  · exact geck_negative_root3_row6 c
  · exact geck_negative_root3_row7 c
  · exact geck_negative_root3_row8 c
  · exact geck_negative_root3_row9 c
  · exact geck_negative_root3_row10 c
  · exact geck_negative_root3_row11 c
  · exact geck_negative_root3_row12 c
  · exact geck_negative_root3_row13 c
  · exact geck_negative_root3_row14 c
  · exact geck_negative_root3_row15 c
  · exact geck_negative_root3_row16 c
  · exact geck_negative_root3_row17 c
  · exact geck_negative_root3_row18 c
  · exact geck_negative_root3_row19 c
  · exact geck_negative_root3_row20 c
  · exact geck_negative_root3_row21 c
  · exact geck_negative_root3_row22 c
  · exact geck_negative_root3_row23 c
  · exact geck_negative_root3_row24 c
  · exact geck_negative_root3_row25 c
  · exact geck_negative_root3_row26 c
  · exact geck_negative_root3_row27 c
  · exact geck_negative_root3_row28 c
  · exact geck_negative_root3_row29 c
  · exact geck_negative_root3_row30 c
  · exact geck_negative_root3_row31 c
  · exact geck_negative_root3_row32 c
  · exact geck_negative_root3_row33 c
  · exact geck_negative_root3_row34 c
  · exact geck_negative_root3_row35 c
  · exact geck_negative_root3_row36 c
  · exact geck_negative_root3_row37 c
  · exact geck_negative_root3_row38 c
  · exact geck_negative_root3_row39 c
  · exact geck_negative_root3_row40 c
  · exact geck_negative_root3_row41 c
  · exact geck_negative_root3_row42 c
  · exact geck_negative_root3_row43 c
  · exact geck_negative_root3_row44 c
  · exact geck_negative_root3_row45 c
  · exact geck_negative_root3_row46 c
  · exact geck_negative_root3_row47 c
  · exact geck_negative_root3_row48 c
  · exact geck_negative_root3_row49 c
  · exact geck_negative_root3_row50 c
  · exact geck_negative_root3_row51 c

private theorem geck_negative_second_root3_row0 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (0 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (0 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row1 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (1 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (1 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row2 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (2 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (2 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row3 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (3 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (3 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row4 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (4 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (4 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row5 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (5 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (5 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row6 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (6 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (6 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row7 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (7 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (7 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row8 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (8 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (8 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row9 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (9 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (9 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row10 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (10 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (10 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row11 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (11 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (11 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row12 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (12 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (12 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row13 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (13 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (13 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row14 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (14 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (14 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row15 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (15 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (15 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row16 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (16 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (16 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row17 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (17 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (17 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row18 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (18 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (18 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row19 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (19 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (19 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row20 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (20 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (20 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row21 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (21 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (21 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row22 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (22 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (22 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row23 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (23 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (23 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row24 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (24 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (24 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row25 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (25 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (25 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row26 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (26 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (26 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row27 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (27 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (27 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row28 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (28 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (28 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row29 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (29 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (29 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row30 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (30 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (30 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row31 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (31 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (31 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row32 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (32 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (32 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row33 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (33 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (33 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row34 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (34 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (34 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row35 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (35 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (35 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row36 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (36 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (36 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row37 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (37 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (37 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row38 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (38 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (38 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row39 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (39 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (39 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row40 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (40 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (40 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row41 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (41 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (41 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row42 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (42 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (42 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row43 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (43 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (43 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row44 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (44 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (44 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row45 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (45 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (45 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row46 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (46 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (46 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row47 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (47 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (47 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row48 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (48 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (48 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row49 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (49 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (49 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row50 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (50 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (50 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

private theorem geck_negative_second_root3_row51 : ∀ c : Fin 52,
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) (51 : Fin 52) c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 (51 : Fin 52))
        (opposite52 c) := by
  unfold geckSecondMatrix opposite52
  decide +kernel

theorem geck_negative_second_root3 : ∀ (a c : Fin 52),
    geckSecondMatrix (Fin.natAdd 4 (3 : Fin 4)) a c =
      geckSecondMatrix (Fin.castAdd 4 (3 : Fin 4)) (opposite52 a) (opposite52 c) := by
  intro a c
  fin_cases a
  · exact geck_negative_second_root3_row0 c
  · exact geck_negative_second_root3_row1 c
  · exact geck_negative_second_root3_row2 c
  · exact geck_negative_second_root3_row3 c
  · exact geck_negative_second_root3_row4 c
  · exact geck_negative_second_root3_row5 c
  · exact geck_negative_second_root3_row6 c
  · exact geck_negative_second_root3_row7 c
  · exact geck_negative_second_root3_row8 c
  · exact geck_negative_second_root3_row9 c
  · exact geck_negative_second_root3_row10 c
  · exact geck_negative_second_root3_row11 c
  · exact geck_negative_second_root3_row12 c
  · exact geck_negative_second_root3_row13 c
  · exact geck_negative_second_root3_row14 c
  · exact geck_negative_second_root3_row15 c
  · exact geck_negative_second_root3_row16 c
  · exact geck_negative_second_root3_row17 c
  · exact geck_negative_second_root3_row18 c
  · exact geck_negative_second_root3_row19 c
  · exact geck_negative_second_root3_row20 c
  · exact geck_negative_second_root3_row21 c
  · exact geck_negative_second_root3_row22 c
  · exact geck_negative_second_root3_row23 c
  · exact geck_negative_second_root3_row24 c
  · exact geck_negative_second_root3_row25 c
  · exact geck_negative_second_root3_row26 c
  · exact geck_negative_second_root3_row27 c
  · exact geck_negative_second_root3_row28 c
  · exact geck_negative_second_root3_row29 c
  · exact geck_negative_second_root3_row30 c
  · exact geck_negative_second_root3_row31 c
  · exact geck_negative_second_root3_row32 c
  · exact geck_negative_second_root3_row33 c
  · exact geck_negative_second_root3_row34 c
  · exact geck_negative_second_root3_row35 c
  · exact geck_negative_second_root3_row36 c
  · exact geck_negative_second_root3_row37 c
  · exact geck_negative_second_root3_row38 c
  · exact geck_negative_second_root3_row39 c
  · exact geck_negative_second_root3_row40 c
  · exact geck_negative_second_root3_row41 c
  · exact geck_negative_second_root3_row42 c
  · exact geck_negative_second_root3_row43 c
  · exact geck_negative_second_root3_row44 c
  · exact geck_negative_second_root3_row45 c
  · exact geck_negative_second_root3_row46 c
  · exact geck_negative_second_root3_row47 c
  · exact geck_negative_second_root3_row48 c
  · exact geck_negative_second_root3_row49 c
  · exact geck_negative_second_root3_row50 c
  · exact geck_negative_second_root3_row51 c

end Atlas.Chevalley.Comparison.F4
