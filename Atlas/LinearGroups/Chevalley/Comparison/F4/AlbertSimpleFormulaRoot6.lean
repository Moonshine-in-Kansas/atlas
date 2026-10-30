import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaData

/-! Root 6: the original 27 private row certificates, unchanged.
Only the final assembled theorem is exported across the module boundary. -/
namespace Atlas.Chevalley.Comparison.F4
open Atlas.Albert
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

variable {R : Type*} [CommRing R]

private theorem albertCoefficient_row_6_0 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleMatrix 6 0 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 0 =
        simpleSecondMatrix 6 0 j := by
  decide +kernel

private theorem albertCoefficient_row_6_1 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleMatrix 6 1 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 1 =
        simpleSecondMatrix 6 1 j := by
  decide +kernel

private theorem albertCoefficient_row_6_2 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleMatrix 6 2 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 2 =
        simpleSecondMatrix 6 2 j := by
  decide +kernel

private theorem albertCoefficient_row_6_3 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleMatrix 6 3 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 3 =
        simpleSecondMatrix 6 3 j := by
  decide +kernel

private theorem albertCoefficient_row_6_4 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleMatrix 6 4 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 4 =
        simpleSecondMatrix 6 4 j := by
  decide +kernel

private theorem albertCoefficient_row_6_5 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleMatrix 6 5 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 5 =
        simpleSecondMatrix 6 5 j := by
  decide +kernel

private theorem albertCoefficient_row_6_6 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleMatrix 6 6 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 6 =
        simpleSecondMatrix 6 6 j := by
  decide +kernel

private theorem albertCoefficient_row_6_7 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleMatrix 6 7 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 7 =
        simpleSecondMatrix 6 7 j := by
  decide +kernel

private theorem albertCoefficient_row_6_8 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleMatrix 6 8 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 8 =
        simpleSecondMatrix 6 8 j := by
  decide +kernel

private theorem albertCoefficient_row_6_9 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleMatrix 6 9 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 9 =
        simpleSecondMatrix 6 9 j := by
  decide +kernel

private theorem albertCoefficient_row_6_10 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleMatrix 6 10 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 10 =
        simpleSecondMatrix 6 10 j := by
  decide +kernel

private theorem albertCoefficient_row_6_11 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleMatrix 6 11 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 11 =
        simpleSecondMatrix 6 11 j := by
  decide +kernel

private theorem albertCoefficient_row_6_12 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleMatrix 6 12 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 12 =
        simpleSecondMatrix 6 12 j := by
  decide +kernel

private theorem albertCoefficient_row_6_13 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleMatrix 6 13 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 13 =
        simpleSecondMatrix 6 13 j := by
  decide +kernel

private theorem albertCoefficient_row_6_14 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleMatrix 6 14 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 14 =
        simpleSecondMatrix 6 14 j := by
  decide +kernel

private theorem albertCoefficient_row_6_15 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleMatrix 6 15 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 15 =
        simpleSecondMatrix 6 15 j := by
  decide +kernel

private theorem albertCoefficient_row_6_16 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleMatrix 6 16 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 16 =
        simpleSecondMatrix 6 16 j := by
  decide +kernel

private theorem albertCoefficient_row_6_17 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleMatrix 6 17 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 17 =
        simpleSecondMatrix 6 17 j := by
  decide +kernel

private theorem albertCoefficient_row_6_18 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleMatrix 6 18 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 18 =
        simpleSecondMatrix 6 18 j := by
  decide +kernel

private theorem albertCoefficient_row_6_19 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleMatrix 6 19 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 19 =
        simpleSecondMatrix 6 19 j := by
  decide +kernel

private theorem albertCoefficient_row_6_20 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleMatrix 6 20 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 20 =
        simpleSecondMatrix 6 20 j := by
  decide +kernel

private theorem albertCoefficient_row_6_21 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleMatrix 6 21 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 21 =
        simpleSecondMatrix 6 21 j := by
  decide +kernel

private theorem albertCoefficient_row_6_22 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleMatrix 6 22 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 22 =
        simpleSecondMatrix 6 22 j := by
  decide +kernel

private theorem albertCoefficient_row_6_23 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleMatrix 6 23 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 23 =
        simpleSecondMatrix 6 23 j := by
  decide +kernel

private theorem albertCoefficient_row_6_24 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleMatrix 6 24 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 24 =
        simpleSecondMatrix 6 24 j := by
  decide +kernel

private theorem albertCoefficient_row_6_25 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleMatrix 6 25 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 25 =
        simpleSecondMatrix 6 25 j := by
  decide +kernel

private theorem albertCoefficient_row_6_26 : ∀ j : Fin 27,
    albertCoordinates
        (albertFirstCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleMatrix 6 26 j ∧
      albertCoordinates
        (albertSecondCoefficient 6
          (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) 26 =
        simpleSecondMatrix 6 26 j := by
  decide +kernel

/-- The two integral coefficients for root 6, assembled from its exact rows. -/
theorem albertCoefficients_integral_root6 (j k : Fin 27) :
    albertCoordinates
        (albertFirstCoefficient 6 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleMatrix 6 k j ∧
      albertCoordinates
        (albertSecondCoefficient 6 (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleSecondMatrix 6 k j := by
  fin_cases k
  · exact albertCoefficient_row_6_0 j
  · exact albertCoefficient_row_6_1 j
  · exact albertCoefficient_row_6_2 j
  · exact albertCoefficient_row_6_3 j
  · exact albertCoefficient_row_6_4 j
  · exact albertCoefficient_row_6_5 j
  · exact albertCoefficient_row_6_6 j
  · exact albertCoefficient_row_6_7 j
  · exact albertCoefficient_row_6_8 j
  · exact albertCoefficient_row_6_9 j
  · exact albertCoefficient_row_6_10 j
  · exact albertCoefficient_row_6_11 j
  · exact albertCoefficient_row_6_12 j
  · exact albertCoefficient_row_6_13 j
  · exact albertCoefficient_row_6_14 j
  · exact albertCoefficient_row_6_15 j
  · exact albertCoefficient_row_6_16 j
  · exact albertCoefficient_row_6_17 j
  · exact albertCoefficient_row_6_18 j
  · exact albertCoefficient_row_6_19 j
  · exact albertCoefficient_row_6_20 j
  · exact albertCoefficient_row_6_21 j
  · exact albertCoefficient_row_6_22 j
  · exact albertCoefficient_row_6_23 j
  · exact albertCoefficient_row_6_24 j
  · exact albertCoefficient_row_6_25 j
  · exact albertCoefficient_row_6_26 j

end Atlas.Chevalley.Comparison.F4
