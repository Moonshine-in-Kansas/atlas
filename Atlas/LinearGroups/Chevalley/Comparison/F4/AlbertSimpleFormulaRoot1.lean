import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaData

/-! Root 1: the original 27 private row certificates, unchanged.
Only the final assembled theorem is exported across the module boundary. -/
namespace Atlas.Chevalley.Comparison.F4
open Atlas.Albert
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

variable {R : Type*} [CommRing R]

private theorem albertCoefficient_row_1_0 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleMatrix 1 0 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleSecondMatrix 1 0 j := by
  decide +kernel

private theorem albertCoefficient_row_1_1 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleMatrix 1 1 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleSecondMatrix 1 1 j := by
  decide +kernel

private theorem albertCoefficient_row_1_2 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleMatrix 1 2 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleSecondMatrix 1 2 j := by
  decide +kernel

private theorem albertCoefficient_row_1_3 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleMatrix 1 3 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleSecondMatrix 1 3 j := by
  decide +kernel

private theorem albertCoefficient_row_1_4 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleMatrix 1 4 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleSecondMatrix 1 4 j := by
  decide +kernel

private theorem albertCoefficient_row_1_5 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleMatrix 1 5 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleSecondMatrix 1 5 j := by
  decide +kernel

private theorem albertCoefficient_row_1_6 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleMatrix 1 6 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleSecondMatrix 1 6 j := by
  decide +kernel

private theorem albertCoefficient_row_1_7 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleMatrix 1 7 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleSecondMatrix 1 7 j := by
  decide +kernel

private theorem albertCoefficient_row_1_8 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleMatrix 1 8 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleSecondMatrix 1 8 j := by
  decide +kernel

private theorem albertCoefficient_row_1_9 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleMatrix 1 9 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleSecondMatrix 1 9 j := by
  decide +kernel

private theorem albertCoefficient_row_1_10 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleMatrix 1 10 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleSecondMatrix 1 10 j := by
  decide +kernel

private theorem albertCoefficient_row_1_11 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleMatrix 1 11 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleSecondMatrix 1 11 j := by
  decide +kernel

private theorem albertCoefficient_row_1_12 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleMatrix 1 12 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleSecondMatrix 1 12 j := by
  decide +kernel

private theorem albertCoefficient_row_1_13 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleMatrix 1 13 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleSecondMatrix 1 13 j := by
  decide +kernel

private theorem albertCoefficient_row_1_14 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleMatrix 1 14 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleSecondMatrix 1 14 j := by
  decide +kernel

private theorem albertCoefficient_row_1_15 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleMatrix 1 15 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleSecondMatrix 1 15 j := by
  decide +kernel

private theorem albertCoefficient_row_1_16 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleMatrix 1 16 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleSecondMatrix 1 16 j := by
  decide +kernel

private theorem albertCoefficient_row_1_17 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleMatrix 1 17 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleSecondMatrix 1 17 j := by
  decide +kernel

private theorem albertCoefficient_row_1_18 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleMatrix 1 18 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleSecondMatrix 1 18 j := by
  decide +kernel

private theorem albertCoefficient_row_1_19 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleMatrix 1 19 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleSecondMatrix 1 19 j := by
  decide +kernel

private theorem albertCoefficient_row_1_20 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleMatrix 1 20 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleSecondMatrix 1 20 j := by
  decide +kernel

private theorem albertCoefficient_row_1_21 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleMatrix 1 21 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleSecondMatrix 1 21 j := by
  decide +kernel

private theorem albertCoefficient_row_1_22 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleMatrix 1 22 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleSecondMatrix 1 22 j := by
  decide +kernel

private theorem albertCoefficient_row_1_23 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleMatrix 1 23 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleSecondMatrix 1 23 j := by
  decide +kernel

private theorem albertCoefficient_row_1_24 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleMatrix 1 24 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleSecondMatrix 1 24 j := by
  decide +kernel

private theorem albertCoefficient_row_1_25 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleMatrix 1 25 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleSecondMatrix 1 25 j := by
  decide +kernel

private theorem albertCoefficient_row_1_26 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleMatrix 1 26 j ∧
      albertCoordinates
        (albertSecondCoefficient 1
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleSecondMatrix 1 26 j := by
  decide +kernel

/-- The two integral coefficients for root 1, assembled from its exact rows. -/
theorem albertCoefficients_integral_root1 (j k : Fin 27) :
    albertCoordinates
        (albertFirstCoefficient 1 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleMatrix 1 k j ∧
      albertCoordinates
        (albertSecondCoefficient 1 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleSecondMatrix 1 k j := by
  fin_cases k
  · exact albertCoefficient_row_1_0 j
  · exact albertCoefficient_row_1_1 j
  · exact albertCoefficient_row_1_2 j
  · exact albertCoefficient_row_1_3 j
  · exact albertCoefficient_row_1_4 j
  · exact albertCoefficient_row_1_5 j
  · exact albertCoefficient_row_1_6 j
  · exact albertCoefficient_row_1_7 j
  · exact albertCoefficient_row_1_8 j
  · exact albertCoefficient_row_1_9 j
  · exact albertCoefficient_row_1_10 j
  · exact albertCoefficient_row_1_11 j
  · exact albertCoefficient_row_1_12 j
  · exact albertCoefficient_row_1_13 j
  · exact albertCoefficient_row_1_14 j
  · exact albertCoefficient_row_1_15 j
  · exact albertCoefficient_row_1_16 j
  · exact albertCoefficient_row_1_17 j
  · exact albertCoefficient_row_1_18 j
  · exact albertCoefficient_row_1_19 j
  · exact albertCoefficient_row_1_20 j
  · exact albertCoefficient_row_1_21 j
  · exact albertCoefficient_row_1_22 j
  · exact albertCoefficient_row_1_23 j
  · exact albertCoefficient_row_1_24 j
  · exact albertCoefficient_row_1_25 j
  · exact albertCoefficient_row_1_26 j

end Atlas.Chevalley.Comparison.F4
