import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaData

/-! Root 4: the original 27 private row certificates, unchanged.
Only the final assembled theorem is exported across the module boundary. -/
namespace Atlas.Chevalley.Comparison.F4
open Atlas.Albert
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

variable {R : Type*} [CommRing R]

private theorem albertCoefficient_row_4_0 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleMatrix 4 0 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleSecondMatrix 4 0 j := by
  decide +kernel

private theorem albertCoefficient_row_4_1 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleMatrix 4 1 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleSecondMatrix 4 1 j := by
  decide +kernel

private theorem albertCoefficient_row_4_2 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleMatrix 4 2 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleSecondMatrix 4 2 j := by
  decide +kernel

private theorem albertCoefficient_row_4_3 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleMatrix 4 3 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleSecondMatrix 4 3 j := by
  decide +kernel

private theorem albertCoefficient_row_4_4 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleMatrix 4 4 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleSecondMatrix 4 4 j := by
  decide +kernel

private theorem albertCoefficient_row_4_5 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleMatrix 4 5 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleSecondMatrix 4 5 j := by
  decide +kernel

private theorem albertCoefficient_row_4_6 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleMatrix 4 6 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleSecondMatrix 4 6 j := by
  decide +kernel

private theorem albertCoefficient_row_4_7 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleMatrix 4 7 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleSecondMatrix 4 7 j := by
  decide +kernel

private theorem albertCoefficient_row_4_8 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleMatrix 4 8 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleSecondMatrix 4 8 j := by
  decide +kernel

private theorem albertCoefficient_row_4_9 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleMatrix 4 9 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleSecondMatrix 4 9 j := by
  decide +kernel

private theorem albertCoefficient_row_4_10 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleMatrix 4 10 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleSecondMatrix 4 10 j := by
  decide +kernel

private theorem albertCoefficient_row_4_11 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleMatrix 4 11 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleSecondMatrix 4 11 j := by
  decide +kernel

private theorem albertCoefficient_row_4_12 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleMatrix 4 12 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleSecondMatrix 4 12 j := by
  decide +kernel

private theorem albertCoefficient_row_4_13 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleMatrix 4 13 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleSecondMatrix 4 13 j := by
  decide +kernel

private theorem albertCoefficient_row_4_14 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleMatrix 4 14 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleSecondMatrix 4 14 j := by
  decide +kernel

private theorem albertCoefficient_row_4_15 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleMatrix 4 15 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleSecondMatrix 4 15 j := by
  decide +kernel

private theorem albertCoefficient_row_4_16 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleMatrix 4 16 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleSecondMatrix 4 16 j := by
  decide +kernel

private theorem albertCoefficient_row_4_17 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleMatrix 4 17 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleSecondMatrix 4 17 j := by
  decide +kernel

private theorem albertCoefficient_row_4_18 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleMatrix 4 18 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleSecondMatrix 4 18 j := by
  decide +kernel

private theorem albertCoefficient_row_4_19 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleMatrix 4 19 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleSecondMatrix 4 19 j := by
  decide +kernel

private theorem albertCoefficient_row_4_20 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleMatrix 4 20 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleSecondMatrix 4 20 j := by
  decide +kernel

private theorem albertCoefficient_row_4_21 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleMatrix 4 21 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleSecondMatrix 4 21 j := by
  decide +kernel

private theorem albertCoefficient_row_4_22 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleMatrix 4 22 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleSecondMatrix 4 22 j := by
  decide +kernel

private theorem albertCoefficient_row_4_23 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleMatrix 4 23 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleSecondMatrix 4 23 j := by
  decide +kernel

private theorem albertCoefficient_row_4_24 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleMatrix 4 24 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleSecondMatrix 4 24 j := by
  decide +kernel

private theorem albertCoefficient_row_4_25 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleMatrix 4 25 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleSecondMatrix 4 25 j := by
  decide +kernel

private theorem albertCoefficient_row_4_26 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleMatrix 4 26 j ∧
      albertCoordinates
        (albertSecondCoefficient 4
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleSecondMatrix 4 26 j := by
  decide +kernel

/-- The two integral coefficients for root 4, assembled from its exact rows. -/
theorem albertCoefficients_integral_root4 (j k : Fin 27) :
    albertCoordinates
        (albertFirstCoefficient 4 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleMatrix 4 k j ∧
      albertCoordinates
        (albertSecondCoefficient 4 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleSecondMatrix 4 k j := by
  fin_cases k
  · exact albertCoefficient_row_4_0 j
  · exact albertCoefficient_row_4_1 j
  · exact albertCoefficient_row_4_2 j
  · exact albertCoefficient_row_4_3 j
  · exact albertCoefficient_row_4_4 j
  · exact albertCoefficient_row_4_5 j
  · exact albertCoefficient_row_4_6 j
  · exact albertCoefficient_row_4_7 j
  · exact albertCoefficient_row_4_8 j
  · exact albertCoefficient_row_4_9 j
  · exact albertCoefficient_row_4_10 j
  · exact albertCoefficient_row_4_11 j
  · exact albertCoefficient_row_4_12 j
  · exact albertCoefficient_row_4_13 j
  · exact albertCoefficient_row_4_14 j
  · exact albertCoefficient_row_4_15 j
  · exact albertCoefficient_row_4_16 j
  · exact albertCoefficient_row_4_17 j
  · exact albertCoefficient_row_4_18 j
  · exact albertCoefficient_row_4_19 j
  · exact albertCoefficient_row_4_20 j
  · exact albertCoefficient_row_4_21 j
  · exact albertCoefficient_row_4_22 j
  · exact albertCoefficient_row_4_23 j
  · exact albertCoefficient_row_4_24 j
  · exact albertCoefficient_row_4_25 j
  · exact albertCoefficient_row_4_26 j

end Atlas.Chevalley.Comparison.F4
