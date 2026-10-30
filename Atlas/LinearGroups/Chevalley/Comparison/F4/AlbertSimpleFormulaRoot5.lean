import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaData

/-! Root 5: the original 27 private row certificates, unchanged.
Only the final assembled theorem is exported across the module boundary. -/
namespace Atlas.Chevalley.Comparison.F4
open Atlas.Albert
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

variable {R : Type*} [CommRing R]

private theorem albertCoefficient_row_5_0 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleMatrix 5 0 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleSecondMatrix 5 0 j := by
  decide +kernel

private theorem albertCoefficient_row_5_1 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleMatrix 5 1 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleSecondMatrix 5 1 j := by
  decide +kernel

private theorem albertCoefficient_row_5_2 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleMatrix 5 2 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleSecondMatrix 5 2 j := by
  decide +kernel

private theorem albertCoefficient_row_5_3 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleMatrix 5 3 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleSecondMatrix 5 3 j := by
  decide +kernel

private theorem albertCoefficient_row_5_4 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleMatrix 5 4 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleSecondMatrix 5 4 j := by
  decide +kernel

private theorem albertCoefficient_row_5_5 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleMatrix 5 5 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleSecondMatrix 5 5 j := by
  decide +kernel

private theorem albertCoefficient_row_5_6 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleMatrix 5 6 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleSecondMatrix 5 6 j := by
  decide +kernel

private theorem albertCoefficient_row_5_7 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleMatrix 5 7 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleSecondMatrix 5 7 j := by
  decide +kernel

private theorem albertCoefficient_row_5_8 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleMatrix 5 8 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleSecondMatrix 5 8 j := by
  decide +kernel

private theorem albertCoefficient_row_5_9 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleMatrix 5 9 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleSecondMatrix 5 9 j := by
  decide +kernel

private theorem albertCoefficient_row_5_10 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleMatrix 5 10 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleSecondMatrix 5 10 j := by
  decide +kernel

private theorem albertCoefficient_row_5_11 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleMatrix 5 11 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleSecondMatrix 5 11 j := by
  decide +kernel

private theorem albertCoefficient_row_5_12 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleMatrix 5 12 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleSecondMatrix 5 12 j := by
  decide +kernel

private theorem albertCoefficient_row_5_13 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleMatrix 5 13 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleSecondMatrix 5 13 j := by
  decide +kernel

private theorem albertCoefficient_row_5_14 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleMatrix 5 14 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleSecondMatrix 5 14 j := by
  decide +kernel

private theorem albertCoefficient_row_5_15 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleMatrix 5 15 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleSecondMatrix 5 15 j := by
  decide +kernel

private theorem albertCoefficient_row_5_16 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleMatrix 5 16 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleSecondMatrix 5 16 j := by
  decide +kernel

private theorem albertCoefficient_row_5_17 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleMatrix 5 17 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleSecondMatrix 5 17 j := by
  decide +kernel

private theorem albertCoefficient_row_5_18 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleMatrix 5 18 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleSecondMatrix 5 18 j := by
  decide +kernel

private theorem albertCoefficient_row_5_19 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleMatrix 5 19 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleSecondMatrix 5 19 j := by
  decide +kernel

private theorem albertCoefficient_row_5_20 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleMatrix 5 20 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleSecondMatrix 5 20 j := by
  decide +kernel

private theorem albertCoefficient_row_5_21 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleMatrix 5 21 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleSecondMatrix 5 21 j := by
  decide +kernel

private theorem albertCoefficient_row_5_22 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleMatrix 5 22 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleSecondMatrix 5 22 j := by
  decide +kernel

private theorem albertCoefficient_row_5_23 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleMatrix 5 23 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleSecondMatrix 5 23 j := by
  decide +kernel

private theorem albertCoefficient_row_5_24 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleMatrix 5 24 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleSecondMatrix 5 24 j := by
  decide +kernel

private theorem albertCoefficient_row_5_25 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleMatrix 5 25 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleSecondMatrix 5 25 j := by
  decide +kernel

private theorem albertCoefficient_row_5_26 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleMatrix 5 26 j ∧
      albertCoordinates
        (albertSecondCoefficient 5
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleSecondMatrix 5 26 j := by
  decide +kernel

/-- The two integral coefficients for root 5, assembled from its exact rows. -/
theorem albertCoefficients_integral_root5 (j k : Fin 27) :
    albertCoordinates
        (albertFirstCoefficient 5 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleMatrix 5 k j ∧
      albertCoordinates
        (albertSecondCoefficient 5 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleSecondMatrix 5 k j := by
  fin_cases k
  · exact albertCoefficient_row_5_0 j
  · exact albertCoefficient_row_5_1 j
  · exact albertCoefficient_row_5_2 j
  · exact albertCoefficient_row_5_3 j
  · exact albertCoefficient_row_5_4 j
  · exact albertCoefficient_row_5_5 j
  · exact albertCoefficient_row_5_6 j
  · exact albertCoefficient_row_5_7 j
  · exact albertCoefficient_row_5_8 j
  · exact albertCoefficient_row_5_9 j
  · exact albertCoefficient_row_5_10 j
  · exact albertCoefficient_row_5_11 j
  · exact albertCoefficient_row_5_12 j
  · exact albertCoefficient_row_5_13 j
  · exact albertCoefficient_row_5_14 j
  · exact albertCoefficient_row_5_15 j
  · exact albertCoefficient_row_5_16 j
  · exact albertCoefficient_row_5_17 j
  · exact albertCoefficient_row_5_18 j
  · exact albertCoefficient_row_5_19 j
  · exact albertCoefficient_row_5_20 j
  · exact albertCoefficient_row_5_21 j
  · exact albertCoefficient_row_5_22 j
  · exact albertCoefficient_row_5_23 j
  · exact albertCoefficient_row_5_24 j
  · exact albertCoefficient_row_5_25 j
  · exact albertCoefficient_row_5_26 j

end Atlas.Chevalley.Comparison.F4
