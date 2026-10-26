import Atlas.Rudvalis.MonomialUR

/-! Kernel-checked nineteen-pivot certificates for the two displayed monomial lifts. -/
namespace Atlas.Rudvalis
open scoped BigOperators

noncomputable def urSeedOperator {R : Type*} [CommRing R] (t : Fin 2) :
    (SeedCoordinate→R) ≃ₗ[R] (SeedCoordinate→R) := if t=0 then seedUOperator else seedROperator

noncomputable def pivotOriginal (i : Fin 19) : SeedCoordinate→ℤ :=
  seedOrbitOriginal (seedOrbitEnumerate (seedPivotIndex i))

def urImageParameterCode (t : Fin 2) (i : Fin 19) : ℕ :=
  ![![2050,393273,2118,448896,2052,421760,439808,2148,403200,458422,411882,41641,74755,68673,122897,95300,3506,337049,149],
    ![2050,393273,2118,458306,2112,421510,430276,2148,403200,448801,412072,32800,337049,330830,377664,356740,3506,74755,149]] t i

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem urPivot_residue_certificate (t : Fin 2) (i : Fin 19) (r : Fin 7) (k : Fin 8) :
    ((signedPositionSign k * urSeedOperator t (pivotOriginal i)
      (r,signedPositionIndex k) : ℤ) : Bit)=
    binaryNormalMap (seedEncodedParameters (urImageParameterCode t i))
      (rowLabel r,seedInnerLabel r k) := by
  decide +kernel +revert

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem urPivot_pair_certificate (t : Fin 2) (i j : Fin 19) :
    4 ∣ ∑ z : SeedCoordinate, urSeedOperator t (pivotOriginal i) z * pivotOriginal j z := by
  decide +kernel +revert

end Atlas.Rudvalis
