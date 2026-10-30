import Atlas.LinearGroups.ReeF4.SpecialIsotropyData

namespace Atlas.ReeF4
variable {F : Type*} [CommRing F] [CharP F 2]

theorem isotropyCross_row0 (x y : Fin 26 → F) :
    isotropyCross x y 0 = (x 2 * y 9 + x 9 * y 2) + (x 3 * y 8 + x 8 * y 3) + (x 4 * y 7 + x 7 * y 4) + (x 5 * y 6 + x 6 * y 5) + (x 18 * y 25 + x 25 * y 18) + (x 19 * y 24 + x 24 * y 19) + (x 20 * y 23 + x 23 * y 20) + (x 21 * y 22 + x 22 * y 21) := by rfl

theorem isotropyCross_row1 (x y : Fin 26 → F) :
    isotropyCross x y 1 = (x 10 * y 17 + x 17 * y 10) + (x 11 * y 16 + x 16 * y 11) + (x 12 * y 15 + x 15 * y 12) + (x 13 * y 14 + x 14 * y 13) + (x 18 * y 25 + x 25 * y 18) + (x 19 * y 24 + x 24 * y 19) + (x 20 * y 23 + x 23 * y 20) + (x 21 * y 22 + x 22 * y 21) := by rfl

theorem isotropyCross_row2 (x y : Fin 26 → F) :
    isotropyCross x y 2 = (x 1 * y 2 + x 2 * y 1) + (x 10 * y 22 + x 22 * y 10) + (x 11 * y 20 + x 20 * y 11) + (x 12 * y 19 + x 19 * y 12) + (x 13 * y 18 + x 18 * y 13) := by rfl

theorem isotropyCross_row3 (x y : Fin 26 → F) :
    isotropyCross x y 3 = (x 1 * y 3 + x 3 * y 1) + (x 10 * y 23 + x 23 * y 10) + (x 11 * y 21 + x 21 * y 11) + (x 14 * y 19 + x 19 * y 14) + (x 15 * y 18 + x 18 * y 15) := by rfl

theorem isotropyCross_row4 (x y : Fin 26 → F) :
    isotropyCross x y 4 = (x 1 * y 4 + x 4 * y 1) + (x 10 * y 24 + x 24 * y 10) + (x 12 * y 21 + x 21 * y 12) + (x 14 * y 20 + x 20 * y 14) + (x 16 * y 18 + x 18 * y 16) := by rfl

theorem isotropyCross_row5 (x y : Fin 26 → F) :
    isotropyCross x y 5 = (x 1 * y 5 + x 5 * y 1) + (x 11 * y 24 + x 24 * y 11) + (x 12 * y 23 + x 23 * y 12) + (x 14 * y 22 + x 22 * y 14) + (x 17 * y 18 + x 18 * y 17) := by rfl

theorem isotropyCross_row6 (x y : Fin 26 → F) :
    isotropyCross x y 6 = (x 1 * y 6 + x 6 * y 1) + (x 10 * y 25 + x 25 * y 10) + (x 13 * y 21 + x 21 * y 13) + (x 15 * y 20 + x 20 * y 15) + (x 16 * y 19 + x 19 * y 16) := by rfl

theorem isotropyCross_row7 (x y : Fin 26 → F) :
    isotropyCross x y 7 = (x 1 * y 7 + x 7 * y 1) + (x 11 * y 25 + x 25 * y 11) + (x 13 * y 23 + x 23 * y 13) + (x 15 * y 22 + x 22 * y 15) + (x 17 * y 19 + x 19 * y 17) := by rfl

theorem isotropyCross_row8 (x y : Fin 26 → F) :
    isotropyCross x y 8 = (x 1 * y 8 + x 8 * y 1) + (x 12 * y 25 + x 25 * y 12) + (x 13 * y 24 + x 24 * y 13) + (x 16 * y 22 + x 22 * y 16) + (x 17 * y 20 + x 20 * y 17) := by rfl

theorem isotropyCross_row9 (x y : Fin 26 → F) :
    isotropyCross x y 9 = (x 1 * y 9 + x 9 * y 1) + (x 14 * y 25 + x 25 * y 14) + (x 15 * y 24 + x 24 * y 15) + (x 16 * y 23 + x 23 * y 16) + (x 17 * y 21 + x 21 * y 17) := by rfl

theorem isotropyCross_row10 (x y : Fin 26 → F) :
    isotropyCross x y 10 = (x 0 * y 10 + x 10 * y 0) + (x 2 * y 21 + x 21 * y 2) + (x 3 * y 20 + x 20 * y 3) + (x 4 * y 19 + x 19 * y 4) + (x 6 * y 18 + x 18 * y 6) := by rfl

theorem isotropyCross_row11 (x y : Fin 26 → F) :
    isotropyCross x y 11 = (x 0 * y 11 + x 11 * y 0) + (x 2 * y 23 + x 23 * y 2) + (x 3 * y 22 + x 22 * y 3) + (x 5 * y 19 + x 19 * y 5) + (x 7 * y 18 + x 18 * y 7) := by rfl

theorem isotropyCross_row12 (x y : Fin 26 → F) :
    isotropyCross x y 12 = (x 0 * y 12 + x 12 * y 0) + (x 2 * y 24 + x 24 * y 2) + (x 4 * y 22 + x 22 * y 4) + (x 5 * y 20 + x 20 * y 5) + (x 8 * y 18 + x 18 * y 8) := by rfl

theorem isotropyCross_row13 (x y : Fin 26 → F) :
    isotropyCross x y 13 = (x 0 * y 13 + x 13 * y 0) + (x 2 * y 25 + x 25 * y 2) + (x 6 * y 22 + x 22 * y 6) + (x 7 * y 20 + x 20 * y 7) + (x 8 * y 19 + x 19 * y 8) := by rfl

theorem isotropyCross_row14 (x y : Fin 26 → F) :
    isotropyCross x y 14 = (x 0 * y 14 + x 14 * y 0) + (x 3 * y 24 + x 24 * y 3) + (x 4 * y 23 + x 23 * y 4) + (x 5 * y 21 + x 21 * y 5) + (x 9 * y 18 + x 18 * y 9) := by rfl

theorem isotropyCross_row15 (x y : Fin 26 → F) :
    isotropyCross x y 15 = (x 0 * y 15 + x 15 * y 0) + (x 3 * y 25 + x 25 * y 3) + (x 6 * y 23 + x 23 * y 6) + (x 7 * y 21 + x 21 * y 7) + (x 9 * y 19 + x 19 * y 9) := by rfl

theorem isotropyCross_row16 (x y : Fin 26 → F) :
    isotropyCross x y 16 = (x 0 * y 16 + x 16 * y 0) + (x 4 * y 25 + x 25 * y 4) + (x 6 * y 24 + x 24 * y 6) + (x 8 * y 21 + x 21 * y 8) + (x 9 * y 20 + x 20 * y 9) := by rfl

theorem isotropyCross_row17 (x y : Fin 26 → F) :
    isotropyCross x y 17 = (x 0 * y 17 + x 17 * y 0) + (x 5 * y 25 + x 25 * y 5) + (x 7 * y 24 + x 24 * y 7) + (x 8 * y 23 + x 23 * y 8) + (x 9 * y 22 + x 22 * y 9) := by rfl

theorem isotropyCross_row18 (x y : Fin 26 → F) :
    isotropyCross x y 18 = (x 0 * y 18 + x 18 * y 0) + (x 1 * y 18 + x 18 * y 1) + (x 2 * y 14 + x 14 * y 2) + (x 3 * y 12 + x 12 * y 3) + (x 4 * y 11 + x 11 * y 4) + (x 5 * y 10 + x 10 * y 5) := by rfl

theorem isotropyCross_row19 (x y : Fin 26 → F) :
    isotropyCross x y 19 = (x 0 * y 19 + x 19 * y 0) + (x 1 * y 19 + x 19 * y 1) + (x 2 * y 15 + x 15 * y 2) + (x 3 * y 13 + x 13 * y 3) + (x 6 * y 11 + x 11 * y 6) + (x 7 * y 10 + x 10 * y 7) := by rfl

theorem isotropyCross_row20 (x y : Fin 26 → F) :
    isotropyCross x y 20 = (x 0 * y 20 + x 20 * y 0) + (x 1 * y 20 + x 20 * y 1) + (x 2 * y 16 + x 16 * y 2) + (x 4 * y 13 + x 13 * y 4) + (x 6 * y 12 + x 12 * y 6) + (x 8 * y 10 + x 10 * y 8) := by rfl

theorem isotropyCross_row21 (x y : Fin 26 → F) :
    isotropyCross x y 21 = (x 0 * y 21 + x 21 * y 0) + (x 1 * y 21 + x 21 * y 1) + (x 3 * y 16 + x 16 * y 3) + (x 4 * y 15 + x 15 * y 4) + (x 6 * y 14 + x 14 * y 6) + (x 9 * y 10 + x 10 * y 9) := by rfl

theorem isotropyCross_row22 (x y : Fin 26 → F) :
    isotropyCross x y 22 = (x 0 * y 22 + x 22 * y 0) + (x 1 * y 22 + x 22 * y 1) + (x 2 * y 17 + x 17 * y 2) + (x 5 * y 13 + x 13 * y 5) + (x 7 * y 12 + x 12 * y 7) + (x 8 * y 11 + x 11 * y 8) := by rfl

theorem isotropyCross_row23 (x y : Fin 26 → F) :
    isotropyCross x y 23 = (x 0 * y 23 + x 23 * y 0) + (x 1 * y 23 + x 23 * y 1) + (x 3 * y 17 + x 17 * y 3) + (x 5 * y 15 + x 15 * y 5) + (x 7 * y 14 + x 14 * y 7) + (x 9 * y 11 + x 11 * y 9) := by rfl

theorem isotropyCross_row24 (x y : Fin 26 → F) :
    isotropyCross x y 24 = (x 0 * y 24 + x 24 * y 0) + (x 1 * y 24 + x 24 * y 1) + (x 4 * y 17 + x 17 * y 4) + (x 5 * y 16 + x 16 * y 5) + (x 8 * y 14 + x 14 * y 8) + (x 9 * y 12 + x 12 * y 9) := by rfl

theorem isotropyCross_row25 (x y : Fin 26 → F) :
    isotropyCross x y 25 = (x 0 * y 25 + x 25 * y 0) + (x 1 * y 25 + x 25 * y 1) + (x 6 * y 17 + x 17 * y 6) + (x 7 * y 16 + x 16 * y 7) + (x 8 * y 15 + x 15 * y 8) + (x 9 * y 13 + x 13 * y 9) := by rfl

theorem isotropyRawStar_row0 (x y : Fin 26 → F) :
    isotropyRawStar x y 0 = (x 3 * y 8 + x 8 * y 3) + (x 4 * y 7 + x 7 * y 4) + (x 11 * y 16 + x 16 * y 11) + (x 12 * y 15 + x 15 * y 12) + (x 19 * y 24 + x 24 * y 19) + (x 20 * y 23 + x 23 * y 20) := by rfl

theorem isotropyRawStar_row1 (x y : Fin 26 → F) :
    isotropyRawStar x y 1 = (x 0 * y 1 + x 1 * y 0) + (x 4 * y 7 + x 7 * y 4) + (x 5 * y 6 + x 6 * y 5) + (x 12 * y 15 + x 15 * y 12) + (x 13 * y 14 + x 14 * y 13) + (x 20 * y 23 + x 23 * y 20) + (x 21 * y 22 + x 22 * y 21) := by rfl

theorem isotropyRawStar_row2 (x y : Fin 26 → F) :
    isotropyRawStar x y 2 = (x 2 * y 3 + x 3 * y 2) + (x 10 * y 11 + x 11 * y 10) + (x 18 * y 19 + x 19 * y 18) := by rfl

theorem isotropyRawStar_row3 (x y : Fin 26 → F) :
    isotropyRawStar x y 3 = (x 2 * y 8 + x 8 * y 2) + (x 12 * y 13 + x 13 * y 12) + (x 20 * y 22 + x 22 * y 20) := by rfl

theorem isotropyRawStar_row4 (x y : Fin 26 → F) :
    isotropyRawStar x y 4 = (x 4 * y 5 + x 5 * y 4) + (x 12 * y 14 + x 14 * y 12) + (x 18 * y 24 + x 24 * y 18) := by rfl

theorem isotropyRawStar_row5 (x y : Fin 26 → F) :
    isotropyRawStar x y 5 = (x 4 * y 6 + x 6 * y 4) + (x 10 * y 16 + x 16 * y 10) + (x 20 * y 21 + x 21 * y 20) := by rfl

theorem isotropyRawStar_row6 (x y : Fin 26 → F) :
    isotropyRawStar x y 6 = (x 5 * y 7 + x 7 * y 5) + (x 11 * y 17 + x 17 * y 11) + (x 22 * y 23 + x 23 * y 22) := by rfl

theorem isotropyRawStar_row7 (x y : Fin 26 → F) :
    isotropyRawStar x y 7 = (x 6 * y 7 + x 7 * y 6) + (x 13 * y 15 + x 15 * y 13) + (x 19 * y 25 + x 25 * y 19) := by rfl

theorem isotropyRawStar_row8 (x y : Fin 26 → F) :
    isotropyRawStar x y 8 = (x 3 * y 9 + x 9 * y 3) + (x 14 * y 15 + x 15 * y 14) + (x 21 * y 23 + x 23 * y 21) := by rfl

theorem isotropyRawStar_row9 (x y : Fin 26 → F) :
    isotropyRawStar x y 9 = (x 8 * y 9 + x 9 * y 8) + (x 16 * y 17 + x 17 * y 16) + (x 24 * y 25 + x 25 * y 24) := by rfl

theorem isotropyRawStar_row10 (x y : Fin 26 → F) :
    isotropyRawStar x y 10 = (x 2 * y 5 + x 5 * y 2) + (x 11 * y 12 + x 12 * y 11) + (x 18 * y 22 + x 22 * y 18) := by rfl

theorem isotropyRawStar_row11 (x y : Fin 26 → F) :
    isotropyRawStar x y 11 = (x 2 * y 6 + x 6 * y 2) + (x 10 * y 13 + x 13 * y 10) + (x 19 * y 20 + x 20 * y 19) := by rfl

theorem isotropyRawStar_row12 (x y : Fin 26 → F) :
    isotropyRawStar x y 12 = (x 3 * y 4 + x 4 * y 3) + (x 10 * y 14 + x 14 * y 10) + (x 18 * y 21 + x 21 * y 18) := by rfl

theorem isotropyRawStar_row13 (x y : Fin 26 → F) :
    isotropyRawStar x y 13 = (x 3 * y 7 + x 7 * y 3) + (x 11 * y 15 + x 15 * y 11) + (x 19 * y 23 + x 23 * y 19) := by rfl

theorem isotropyRawStar_row14 (x y : Fin 26 → F) :
    isotropyRawStar x y 14 = (x 4 * y 8 + x 8 * y 4) + (x 12 * y 16 + x 16 * y 12) + (x 20 * y 24 + x 24 * y 20) := by rfl

theorem isotropyRawStar_row15 (x y : Fin 26 → F) :
    isotropyRawStar x y 15 = (x 7 * y 8 + x 8 * y 7) + (x 13 * y 17 + x 17 * y 13) + (x 22 * y 25 + x 25 * y 22) := by rfl

theorem isotropyRawStar_row16 (x y : Fin 26 → F) :
    isotropyRawStar x y 16 = (x 5 * y 9 + x 9 * y 5) + (x 14 * y 17 + x 17 * y 14) + (x 23 * y 24 + x 24 * y 23) := by rfl

theorem isotropyRawStar_row17 (x y : Fin 26 → F) :
    isotropyRawStar x y 17 = (x 6 * y 9 + x 9 * y 6) + (x 15 * y 16 + x 16 * y 15) + (x 21 * y 25 + x 25 * y 21) := by rfl

theorem isotropyRawStar_row18 (x y : Fin 26 → F) :
    isotropyRawStar x y 18 = (x 2 * y 4 + x 4 * y 2) + (x 10 * y 12 + x 12 * y 10) + (x 18 * y 20 + x 20 * y 18) := by rfl

theorem isotropyRawStar_row19 (x y : Fin 26 → F) :
    isotropyRawStar x y 19 = (x 2 * y 7 + x 7 * y 2) + (x 11 * y 13 + x 13 * y 11) + (x 19 * y 22 + x 22 * y 19) := by rfl

theorem isotropyRawStar_row20 (x y : Fin 26 → F) :
    isotropyRawStar x y 20 = (x 3 * y 5 + x 5 * y 3) + (x 11 * y 14 + x 14 * y 11) + (x 18 * y 23 + x 23 * y 18) := by rfl

theorem isotropyRawStar_row21 (x y : Fin 26 → F) :
    isotropyRawStar x y 21 = (x 5 * y 8 + x 8 * y 5) + (x 12 * y 17 + x 17 * y 12) + (x 22 * y 24 + x 24 * y 22) := by rfl

theorem isotropyRawStar_row22 (x y : Fin 26 → F) :
    isotropyRawStar x y 22 = (x 3 * y 6 + x 6 * y 3) + (x 10 * y 15 + x 15 * y 10) + (x 19 * y 21 + x 21 * y 19) := by rfl

theorem isotropyRawStar_row23 (x y : Fin 26 → F) :
    isotropyRawStar x y 23 = (x 6 * y 8 + x 8 * y 6) + (x 13 * y 16 + x 16 * y 13) + (x 20 * y 25 + x 25 * y 20) := by rfl

theorem isotropyRawStar_row24 (x y : Fin 26 → F) :
    isotropyRawStar x y 24 = (x 4 * y 9 + x 9 * y 4) + (x 14 * y 16 + x 16 * y 14) + (x 21 * y 24 + x 24 * y 21) := by rfl

theorem isotropyRawStar_row25 (x y : Fin 26 → F) :
    isotropyRawStar x y 25 = (x 7 * y 9 + x 9 * y 7) + (x 15 * y 17 + x 17 * y 15) + (x 23 * y 25 + x 25 * y 23) := by rfl

end Atlas.ReeF4
