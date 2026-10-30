import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaData

/-! Root 2: the original 27 private row certificates, unchanged.
Only the final assembled theorem is exported across the module boundary. -/
namespace Atlas.Chevalley.Comparison.F4
open Atlas.Albert
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

variable {R : Type*} [CommRing R]

private theorem albertCoefficient_row_2_0 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleMatrix 2 0 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleSecondMatrix 2 0 j := by
  decide +kernel

private theorem albertCoefficient_row_2_1 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleMatrix 2 1 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleSecondMatrix 2 1 j := by
  decide +kernel

private theorem albertCoefficient_row_2_2 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleMatrix 2 2 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleSecondMatrix 2 2 j := by
  decide +kernel

private theorem albertCoefficient_row_2_3 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleMatrix 2 3 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleSecondMatrix 2 3 j := by
  decide +kernel

private theorem albertCoefficient_row_2_4 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleMatrix 2 4 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleSecondMatrix 2 4 j := by
  decide +kernel

private theorem albertCoefficient_row_2_5 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleMatrix 2 5 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleSecondMatrix 2 5 j := by
  decide +kernel

private theorem albertCoefficient_row_2_6 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleMatrix 2 6 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleSecondMatrix 2 6 j := by
  decide +kernel

private theorem albertCoefficient_row_2_7 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleMatrix 2 7 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleSecondMatrix 2 7 j := by
  decide +kernel

private theorem albertCoefficient_row_2_8 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleMatrix 2 8 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleSecondMatrix 2 8 j := by
  decide +kernel

private theorem albertCoefficient_row_2_9 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleMatrix 2 9 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleSecondMatrix 2 9 j := by
  decide +kernel

private theorem albertCoefficient_row_2_10 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleMatrix 2 10 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleSecondMatrix 2 10 j := by
  decide +kernel

private theorem albertCoefficient_row_2_11 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleMatrix 2 11 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleSecondMatrix 2 11 j := by
  decide +kernel

private theorem albertCoefficient_row_2_12 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleMatrix 2 12 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleSecondMatrix 2 12 j := by
  decide +kernel

private theorem albertCoefficient_row_2_13 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleMatrix 2 13 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleSecondMatrix 2 13 j := by
  decide +kernel

private theorem albertCoefficient_row_2_14 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleMatrix 2 14 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleSecondMatrix 2 14 j := by
  decide +kernel

private theorem albertCoefficient_row_2_15 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleMatrix 2 15 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleSecondMatrix 2 15 j := by
  decide +kernel

private theorem albertCoefficient_row_2_16 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleMatrix 2 16 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleSecondMatrix 2 16 j := by
  decide +kernel

private theorem albertCoefficient_row_2_17 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleMatrix 2 17 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleSecondMatrix 2 17 j := by
  decide +kernel

private theorem albertCoefficient_row_2_18 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleMatrix 2 18 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleSecondMatrix 2 18 j := by
  decide +kernel

private theorem albertCoefficient_row_2_19 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleMatrix 2 19 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleSecondMatrix 2 19 j := by
  decide +kernel

private theorem albertCoefficient_row_2_20 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleMatrix 2 20 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleSecondMatrix 2 20 j := by
  decide +kernel

private theorem albertCoefficient_row_2_21 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleMatrix 2 21 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleSecondMatrix 2 21 j := by
  decide +kernel

private theorem albertCoefficient_row_2_22 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleMatrix 2 22 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleSecondMatrix 2 22 j := by
  decide +kernel

private theorem albertCoefficient_row_2_23 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleMatrix 2 23 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleSecondMatrix 2 23 j := by
  decide +kernel

private theorem albertCoefficient_row_2_24 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleMatrix 2 24 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleSecondMatrix 2 24 j := by
  decide +kernel

private theorem albertCoefficient_row_2_25 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleMatrix 2 25 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleSecondMatrix 2 25 j := by
  decide +kernel

private theorem albertCoefficient_row_2_26 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleMatrix 2 26 j ∧
      albertCoordinates
        (albertSecondCoefficient 2
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleSecondMatrix 2 26 j := by
  decide +kernel

/-- The two integral coefficients for root 2, assembled from its exact rows. -/
theorem albertCoefficients_integral_root2 (j k : Fin 27) :
    albertCoordinates
        (albertFirstCoefficient 2 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleMatrix 2 k j ∧
      albertCoordinates
        (albertSecondCoefficient 2 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleSecondMatrix 2 k j := by
  fin_cases k
  · exact albertCoefficient_row_2_0 j
  · exact albertCoefficient_row_2_1 j
  · exact albertCoefficient_row_2_2 j
  · exact albertCoefficient_row_2_3 j
  · exact albertCoefficient_row_2_4 j
  · exact albertCoefficient_row_2_5 j
  · exact albertCoefficient_row_2_6 j
  · exact albertCoefficient_row_2_7 j
  · exact albertCoefficient_row_2_8 j
  · exact albertCoefficient_row_2_9 j
  · exact albertCoefficient_row_2_10 j
  · exact albertCoefficient_row_2_11 j
  · exact albertCoefficient_row_2_12 j
  · exact albertCoefficient_row_2_13 j
  · exact albertCoefficient_row_2_14 j
  · exact albertCoefficient_row_2_15 j
  · exact albertCoefficient_row_2_16 j
  · exact albertCoefficient_row_2_17 j
  · exact albertCoefficient_row_2_18 j
  · exact albertCoefficient_row_2_19 j
  · exact albertCoefficient_row_2_20 j
  · exact albertCoefficient_row_2_21 j
  · exact albertCoefficient_row_2_22 j
  · exact albertCoefficient_row_2_23 j
  · exact albertCoefficient_row_2_24 j
  · exact albertCoefficient_row_2_25 j
  · exact albertCoefficient_row_2_26 j

end Atlas.Chevalley.Comparison.F4
