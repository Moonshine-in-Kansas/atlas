import F4Work.F4AlbertSimpleFormulaData

/-! Root 3: the original 27 private row certificates, unchanged.
Only the final assembled theorem is exported across the module boundary. -/
namespace Atlas.Chevalley.Comparison.F4
open Atlas.Albert
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

variable {R : Type*} [CommRing R]

private theorem albertCoefficient_row_3_0 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleMatrix 3 0 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleSecondMatrix 3 0 j := by
  decide +kernel

private theorem albertCoefficient_row_3_1 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleMatrix 3 1 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleSecondMatrix 3 1 j := by
  decide +kernel

private theorem albertCoefficient_row_3_2 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleMatrix 3 2 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleSecondMatrix 3 2 j := by
  decide +kernel

private theorem albertCoefficient_row_3_3 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleMatrix 3 3 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleSecondMatrix 3 3 j := by
  decide +kernel

private theorem albertCoefficient_row_3_4 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleMatrix 3 4 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleSecondMatrix 3 4 j := by
  decide +kernel

private theorem albertCoefficient_row_3_5 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleMatrix 3 5 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleSecondMatrix 3 5 j := by
  decide +kernel

private theorem albertCoefficient_row_3_6 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleMatrix 3 6 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleSecondMatrix 3 6 j := by
  decide +kernel

private theorem albertCoefficient_row_3_7 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleMatrix 3 7 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleSecondMatrix 3 7 j := by
  decide +kernel

private theorem albertCoefficient_row_3_8 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleMatrix 3 8 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleSecondMatrix 3 8 j := by
  decide +kernel

private theorem albertCoefficient_row_3_9 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleMatrix 3 9 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleSecondMatrix 3 9 j := by
  decide +kernel

private theorem albertCoefficient_row_3_10 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleMatrix 3 10 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleSecondMatrix 3 10 j := by
  decide +kernel

private theorem albertCoefficient_row_3_11 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleMatrix 3 11 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleSecondMatrix 3 11 j := by
  decide +kernel

private theorem albertCoefficient_row_3_12 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleMatrix 3 12 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleSecondMatrix 3 12 j := by
  decide +kernel

private theorem albertCoefficient_row_3_13 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleMatrix 3 13 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleSecondMatrix 3 13 j := by
  decide +kernel

private theorem albertCoefficient_row_3_14 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleMatrix 3 14 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleSecondMatrix 3 14 j := by
  decide +kernel

private theorem albertCoefficient_row_3_15 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleMatrix 3 15 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleSecondMatrix 3 15 j := by
  decide +kernel

private theorem albertCoefficient_row_3_16 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleMatrix 3 16 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleSecondMatrix 3 16 j := by
  decide +kernel

private theorem albertCoefficient_row_3_17 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleMatrix 3 17 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleSecondMatrix 3 17 j := by
  decide +kernel

private theorem albertCoefficient_row_3_18 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleMatrix 3 18 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleSecondMatrix 3 18 j := by
  decide +kernel

private theorem albertCoefficient_row_3_19 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleMatrix 3 19 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleSecondMatrix 3 19 j := by
  decide +kernel

private theorem albertCoefficient_row_3_20 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleMatrix 3 20 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleSecondMatrix 3 20 j := by
  decide +kernel

private theorem albertCoefficient_row_3_21 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleMatrix 3 21 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleSecondMatrix 3 21 j := by
  decide +kernel

private theorem albertCoefficient_row_3_22 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleMatrix 3 22 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleSecondMatrix 3 22 j := by
  decide +kernel

private theorem albertCoefficient_row_3_23 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleMatrix 3 23 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleSecondMatrix 3 23 j := by
  decide +kernel

private theorem albertCoefficient_row_3_24 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleMatrix 3 24 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleSecondMatrix 3 24 j := by
  decide +kernel

private theorem albertCoefficient_row_3_25 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleMatrix 3 25 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleSecondMatrix 3 25 j := by
  decide +kernel

private theorem albertCoefficient_row_3_26 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleMatrix 3 26 j ∧
      albertCoordinates
        (albertSecondCoefficient 3
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleSecondMatrix 3 26 j := by
  decide +kernel

/-- The two integral coefficients for root 3, assembled from its exact rows. -/
theorem albertCoefficients_integral_root3 (j k : Fin 27) :
    albertCoordinates
        (albertFirstCoefficient 3 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleMatrix 3 k j ∧
      albertCoordinates
        (albertSecondCoefficient 3 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleSecondMatrix 3 k j := by
  fin_cases k
  · exact albertCoefficient_row_3_0 j
  · exact albertCoefficient_row_3_1 j
  · exact albertCoefficient_row_3_2 j
  · exact albertCoefficient_row_3_3 j
  · exact albertCoefficient_row_3_4 j
  · exact albertCoefficient_row_3_5 j
  · exact albertCoefficient_row_3_6 j
  · exact albertCoefficient_row_3_7 j
  · exact albertCoefficient_row_3_8 j
  · exact albertCoefficient_row_3_9 j
  · exact albertCoefficient_row_3_10 j
  · exact albertCoefficient_row_3_11 j
  · exact albertCoefficient_row_3_12 j
  · exact albertCoefficient_row_3_13 j
  · exact albertCoefficient_row_3_14 j
  · exact albertCoefficient_row_3_15 j
  · exact albertCoefficient_row_3_16 j
  · exact albertCoefficient_row_3_17 j
  · exact albertCoefficient_row_3_18 j
  · exact albertCoefficient_row_3_19 j
  · exact albertCoefficient_row_3_20 j
  · exact albertCoefficient_row_3_21 j
  · exact albertCoefficient_row_3_22 j
  · exact albertCoefficient_row_3_23 j
  · exact albertCoefficient_row_3_24 j
  · exact albertCoefficient_row_3_25 j
  · exact albertCoefficient_row_3_26 j

end Atlas.Chevalley.Comparison.F4
