import Atlas.Fischer.CountingSourceColumns

namespace Atlas.Fischer
open scoped BigOperators

abbrev CountingColumnVector := Fin 6 → ℕ

/-- The two allowed intersection sizes, with their actual delta values. -/
def countingColumnDelta (n : ℕ) : Option ℕ :=
  if n=0 then some 1 else if n=4 then some 0 else none

/-- The column sizes of G diamond H, with complement taken after symmetric difference. -/
def countingDiamondColumns (d : ℕ) (g b h : CountingColumnVector) : CountingColumnVector :=
  fun i => if d=0 then g i+b i-2*h i else 4-(g i+b i-2*h i)

/-- Literal source column-count-rule followed by signed-octad-summand.
The interpretation for actual octads is proved separately from this finite arithmetic. -/
def countingColumnWeight (epsilon : ℕ) (D E F : Finset (Fin 6))
    (g b h : CountingColumnVector) : Option ℤ := do
  let d0 ← countingColumnDelta (∑ i, h i)
  let d1 ← countingColumnDelta (∑ i ∈ D, g i)
  let d2 ← countingColumnDelta (∑ i ∈ E, b i)
  let j := countingDiamondColumns d0 g b h
  let d3 ← countingColumnDelta (∑ i ∈ F, j i)
  let d4 := (epsilon+d0+d1+d2+d3)%2
  let s := (∑ i ∈ E, g i)/2+(∑ i ∈ D ∩ E, b i)+(∑ i ∈ D, h i)
  return (-1 : ℤ)^(s+d0+d4)*(-3 : ℤ)^((d0+d1+d2+d3+d4-epsilon)/2)

/-- The six possible signed nonzero weights, in increasing order. -/
def countingSignedWeight (i : Fin 6) : ℤ := ![-9,-3,-1,1,3,9] i

abbrev CountingSignedHistogram := Fin 6 → ℕ

def countingWeightHistogram (w : Option ℤ) : CountingSignedHistogram :=
  fun i => if w=some (countingSignedWeight i) then 1 else 0

/-- The derivative at one of the source Laurent polynomial, retaining every sign. -/
def countingHistogramMoment (v : CountingSignedHistogram) : ℤ :=
  ∑ i, countingSignedWeight i*(v i : ℤ)

end Atlas.Fischer
