import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaData

/-! Root 7: the original 27 private row certificates, unchanged.
Only the final assembled theorem is exported across the module boundary. -/
namespace Atlas.Chevalley.Comparison.F4
open Atlas.Albert
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

variable {R : Type*} [CommRing R]

private theorem albertCoefficient_row_7_0 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleMatrix 7 0 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleSecondMatrix 7 0 j := by
  decide +kernel

private theorem albertCoefficient_row_7_1 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleMatrix 7 1 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleSecondMatrix 7 1 j := by
  decide +kernel

private theorem albertCoefficient_row_7_2 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleMatrix 7 2 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleSecondMatrix 7 2 j := by
  decide +kernel

private theorem albertCoefficient_row_7_3 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleMatrix 7 3 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleSecondMatrix 7 3 j := by
  decide +kernel

private theorem albertCoefficient_row_7_4 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleMatrix 7 4 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleSecondMatrix 7 4 j := by
  decide +kernel

private theorem albertCoefficient_row_7_5 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleMatrix 7 5 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleSecondMatrix 7 5 j := by
  decide +kernel

private theorem albertCoefficient_row_7_6 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleMatrix 7 6 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleSecondMatrix 7 6 j := by
  decide +kernel

private theorem albertCoefficient_row_7_7 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleMatrix 7 7 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleSecondMatrix 7 7 j := by
  decide +kernel

private theorem albertCoefficient_row_7_8 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleMatrix 7 8 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleSecondMatrix 7 8 j := by
  decide +kernel

private theorem albertCoefficient_row_7_9 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleMatrix 7 9 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleSecondMatrix 7 9 j := by
  decide +kernel

private theorem albertCoefficient_row_7_10 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleMatrix 7 10 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleSecondMatrix 7 10 j := by
  decide +kernel

private theorem albertCoefficient_row_7_11 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleMatrix 7 11 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleSecondMatrix 7 11 j := by
  decide +kernel

private theorem albertCoefficient_row_7_12 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleMatrix 7 12 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleSecondMatrix 7 12 j := by
  decide +kernel

private theorem albertCoefficient_row_7_13 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleMatrix 7 13 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleSecondMatrix 7 13 j := by
  decide +kernel

private theorem albertCoefficient_row_7_14 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleMatrix 7 14 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleSecondMatrix 7 14 j := by
  decide +kernel

private theorem albertCoefficient_row_7_15 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleMatrix 7 15 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleSecondMatrix 7 15 j := by
  decide +kernel

private theorem albertCoefficient_row_7_16 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleMatrix 7 16 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleSecondMatrix 7 16 j := by
  decide +kernel

private theorem albertCoefficient_row_7_17 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleMatrix 7 17 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleSecondMatrix 7 17 j := by
  decide +kernel

private theorem albertCoefficient_row_7_18 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleMatrix 7 18 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleSecondMatrix 7 18 j := by
  decide +kernel

private theorem albertCoefficient_row_7_19 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleMatrix 7 19 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleSecondMatrix 7 19 j := by
  decide +kernel

private theorem albertCoefficient_row_7_20 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleMatrix 7 20 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleSecondMatrix 7 20 j := by
  decide +kernel

private theorem albertCoefficient_row_7_21 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleMatrix 7 21 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleSecondMatrix 7 21 j := by
  decide +kernel

private theorem albertCoefficient_row_7_22 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleMatrix 7 22 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleSecondMatrix 7 22 j := by
  decide +kernel

private theorem albertCoefficient_row_7_23 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleMatrix 7 23 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleSecondMatrix 7 23 j := by
  decide +kernel

private theorem albertCoefficient_row_7_24 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleMatrix 7 24 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleSecondMatrix 7 24 j := by
  decide +kernel

private theorem albertCoefficient_row_7_25 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleMatrix 7 25 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleSecondMatrix 7 25 j := by
  decide +kernel

private theorem albertCoefficient_row_7_26 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleMatrix 7 26 j ∧
      albertCoordinates
        (albertSecondCoefficient 7
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleSecondMatrix 7 26 j := by
  decide +kernel

/-- The two integral coefficients for root 7, assembled from its exact rows. -/
theorem albertCoefficients_integral_root7 (j k : Fin 27) :
    albertCoordinates
        (albertFirstCoefficient 7 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleMatrix 7 k j ∧
      albertCoordinates
        (albertSecondCoefficient 7 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleSecondMatrix 7 k j := by
  fin_cases k
  · exact albertCoefficient_row_7_0 j
  · exact albertCoefficient_row_7_1 j
  · exact albertCoefficient_row_7_2 j
  · exact albertCoefficient_row_7_3 j
  · exact albertCoefficient_row_7_4 j
  · exact albertCoefficient_row_7_5 j
  · exact albertCoefficient_row_7_6 j
  · exact albertCoefficient_row_7_7 j
  · exact albertCoefficient_row_7_8 j
  · exact albertCoefficient_row_7_9 j
  · exact albertCoefficient_row_7_10 j
  · exact albertCoefficient_row_7_11 j
  · exact albertCoefficient_row_7_12 j
  · exact albertCoefficient_row_7_13 j
  · exact albertCoefficient_row_7_14 j
  · exact albertCoefficient_row_7_15 j
  · exact albertCoefficient_row_7_16 j
  · exact albertCoefficient_row_7_17 j
  · exact albertCoefficient_row_7_18 j
  · exact albertCoefficient_row_7_19 j
  · exact albertCoefficient_row_7_20 j
  · exact albertCoefficient_row_7_21 j
  · exact albertCoefficient_row_7_22 j
  · exact albertCoefficient_row_7_23 j
  · exact albertCoefficient_row_7_24 j
  · exact albertCoefficient_row_7_25 j
  · exact albertCoefficient_row_7_26 j

end Atlas.Chevalley.Comparison.F4
