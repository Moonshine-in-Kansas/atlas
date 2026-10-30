import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaData

/-! Root 0: the original 27 private row certificates, unchanged.
Only the final assembled theorem is exported across the module boundary. -/
namespace Atlas.Chevalley.Comparison.F4
open Atlas.Albert
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

variable {R : Type*} [CommRing R]

private theorem albertCoefficient_row_0_0 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleMatrix 0 0 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleSecondMatrix 0 0 j := by
  decide +kernel

private theorem albertCoefficient_row_0_1 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleMatrix 0 1 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleSecondMatrix 0 1 j := by
  decide +kernel

private theorem albertCoefficient_row_0_2 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleMatrix 0 2 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleSecondMatrix 0 2 j := by
  decide +kernel

private theorem albertCoefficient_row_0_3 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleMatrix 0 3 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleSecondMatrix 0 3 j := by
  decide +kernel

private theorem albertCoefficient_row_0_4 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleMatrix 0 4 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleSecondMatrix 0 4 j := by
  decide +kernel

private theorem albertCoefficient_row_0_5 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleMatrix 0 5 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleSecondMatrix 0 5 j := by
  decide +kernel

private theorem albertCoefficient_row_0_6 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleMatrix 0 6 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleSecondMatrix 0 6 j := by
  decide +kernel

private theorem albertCoefficient_row_0_7 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleMatrix 0 7 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleSecondMatrix 0 7 j := by
  decide +kernel

private theorem albertCoefficient_row_0_8 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleMatrix 0 8 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleSecondMatrix 0 8 j := by
  decide +kernel

private theorem albertCoefficient_row_0_9 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleMatrix 0 9 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleSecondMatrix 0 9 j := by
  decide +kernel

private theorem albertCoefficient_row_0_10 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleMatrix 0 10 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleSecondMatrix 0 10 j := by
  decide +kernel

private theorem albertCoefficient_row_0_11 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleMatrix 0 11 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleSecondMatrix 0 11 j := by
  decide +kernel

private theorem albertCoefficient_row_0_12 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleMatrix 0 12 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleSecondMatrix 0 12 j := by
  decide +kernel

private theorem albertCoefficient_row_0_13 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleMatrix 0 13 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleSecondMatrix 0 13 j := by
  decide +kernel

private theorem albertCoefficient_row_0_14 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleMatrix 0 14 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleSecondMatrix 0 14 j := by
  decide +kernel

private theorem albertCoefficient_row_0_15 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleMatrix 0 15 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleSecondMatrix 0 15 j := by
  decide +kernel

private theorem albertCoefficient_row_0_16 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleMatrix 0 16 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleSecondMatrix 0 16 j := by
  decide +kernel

private theorem albertCoefficient_row_0_17 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleMatrix 0 17 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleSecondMatrix 0 17 j := by
  decide +kernel

private theorem albertCoefficient_row_0_18 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleMatrix 0 18 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleSecondMatrix 0 18 j := by
  decide +kernel

private theorem albertCoefficient_row_0_19 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleMatrix 0 19 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleSecondMatrix 0 19 j := by
  decide +kernel

private theorem albertCoefficient_row_0_20 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleMatrix 0 20 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleSecondMatrix 0 20 j := by
  decide +kernel

private theorem albertCoefficient_row_0_21 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleMatrix 0 21 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleSecondMatrix 0 21 j := by
  decide +kernel

private theorem albertCoefficient_row_0_22 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleMatrix 0 22 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleSecondMatrix 0 22 j := by
  decide +kernel

private theorem albertCoefficient_row_0_23 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleMatrix 0 23 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleSecondMatrix 0 23 j := by
  decide +kernel

private theorem albertCoefficient_row_0_24 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleMatrix 0 24 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleSecondMatrix 0 24 j := by
  decide +kernel

private theorem albertCoefficient_row_0_25 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleMatrix 0 25 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleSecondMatrix 0 25 j := by
  decide +kernel

private theorem albertCoefficient_row_0_26 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleMatrix 0 26 j ∧
      albertCoordinates
        (albertSecondCoefficient 0
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleSecondMatrix 0 26 j := by
  decide +kernel

/-- The two integral coefficients for root 0, assembled from its exact rows. -/
theorem albertCoefficients_integral_root0 (j k : Fin 27) :
    albertCoordinates
        (albertFirstCoefficient 0 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleMatrix 0 k j ∧
      albertCoordinates
        (albertSecondCoefficient 0 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleSecondMatrix 0 k j := by
  fin_cases k
  · exact albertCoefficient_row_0_0 j
  · exact albertCoefficient_row_0_1 j
  · exact albertCoefficient_row_0_2 j
  · exact albertCoefficient_row_0_3 j
  · exact albertCoefficient_row_0_4 j
  · exact albertCoefficient_row_0_5 j
  · exact albertCoefficient_row_0_6 j
  · exact albertCoefficient_row_0_7 j
  · exact albertCoefficient_row_0_8 j
  · exact albertCoefficient_row_0_9 j
  · exact albertCoefficient_row_0_10 j
  · exact albertCoefficient_row_0_11 j
  · exact albertCoefficient_row_0_12 j
  · exact albertCoefficient_row_0_13 j
  · exact albertCoefficient_row_0_14 j
  · exact albertCoefficient_row_0_15 j
  · exact albertCoefficient_row_0_16 j
  · exact albertCoefficient_row_0_17 j
  · exact albertCoefficient_row_0_18 j
  · exact albertCoefficient_row_0_19 j
  · exact albertCoefficient_row_0_20 j
  · exact albertCoefficient_row_0_21 j
  · exact albertCoefficient_row_0_22 j
  · exact albertCoefficient_row_0_23 j
  · exact albertCoefficient_row_0_24 j
  · exact albertCoefficient_row_0_25 j
  · exact albertCoefficient_row_0_26 j

end Atlas.Chevalley.Comparison.F4
