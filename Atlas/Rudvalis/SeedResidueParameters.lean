import Atlas.Rudvalis.SeedSignedOperators

/-! Small explicit linear certificates for the binary layer of the 112 defining seeds.
The certificates are checked in Lean; no enumeration of the full code is used. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def seedEncodedParameters (n : ℕ) : BinaryParameters :=
  ((fun p => if p.val=binaryLabel 1 then (n : Bit)
    else if p.val=binaryLabel 2 then ((n/2 : ℕ) : Bit)
    else if p.val=binaryLabel 3 then ((n/4 : ℕ) : Bit)
    else if p.val=binaryLabel 4 then ((n/8 : ℕ) : Bit)
    else if p.val=binaryLabel 5 then ((n/16 : ℕ) : Bit)
    else if p.val=binaryLabel 6 then ((n/32 : ℕ) : Bit)
    else ((n/64 : ℕ) : Bit)),
    (fun j i => ((n/2^(7+3*j.val+i.val) : ℕ) : Bit)),
    (fun i => ((n/2^(16+i.val) : ℕ) : Bit)))

def seedOrbitEnumerate (n : Fin 112) : SeedOrbitIndex :=
  (⟨n.val/16,by omega⟩,⟨n.val/8%2,Nat.mod_lt _ (by decide)⟩,
    ⟨n.val/2%4,Nat.mod_lt _ (by decide)⟩,⟨n.val%2,Nat.mod_lt _ (by decide)⟩)

def seedOrbitParameterCode : Fin 112 → ℕ :=
  ![2118,393273,2050,448896,2112,421760,2052,439808,2080,403200,2148,458422,2086,411882,2146,430437,41644,65619,41604,75776,41608,115712,41632,125952,41601,86016,41641,96357,41637,103439,41613,113721,3491,327772,3488,340096,3458,379648,3457,392064,3472,349440,3475,353721,3505,368182,3506,372435,149,458858,129,520576,132,502656,144,481792,192,489216,212,493267,209,515301,197,470364,32880,262159,32784,268416,32800,265984,32832,268160,32776,263424,32872,269788,32856,264761,32824,266986,65481,131126,65472,180480,65409,155776,65416,172416,65410,139776,65419,189290,65482,148179,65475,164751,55322,196709,55304,256256,55312,238720,55298,216448,55300,225792,55318,236303,55310,251612,55324,212918]

noncomputable def seedOrbitResidue (t : SeedOrbitIndex) : BinaryWord :=
  fun z => (seedOrbitWord t z : Bit)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem seedOrbitResidue_parameters (n : Fin 112) :
    seedOrbitResidue (seedOrbitEnumerate n)=
      binaryNormalMap (seedEncodedParameters (seedOrbitParameterCode n)) := by
  funext z
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  change (signedSeedTransport (seedOrbitOriginal (seedOrbitEnumerate n))
    (seedCoordinateEquiv (r,k)) : Bit)=_
  rw [signedSeedTransport_apply]
  change ((signedPositionSign k * seedOrbitOriginal (seedOrbitEnumerate n)
    (r,signedPositionIndex k) : ℤ) : Bit)=
    binaryNormalMap (seedEncodedParameters (seedOrbitParameterCode n))
      (rowLabel r,seedInnerLabel r k)
  decide +kernel +revert

end Atlas.Rudvalis
