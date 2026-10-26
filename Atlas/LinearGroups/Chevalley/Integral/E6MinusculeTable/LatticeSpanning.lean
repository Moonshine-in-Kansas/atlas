import Atlas.LinearGroups.Chevalley.Integral.E6MinusculeTable.Data

/-! E6 minuscule certificate component: LatticeSpanning. -/
namespace Atlas.Chevalley.E6MinusculeTable
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def spanningCoefficientsTable : Array (Array ℤ) := #[#[0,0,0,0,0,0],#[1,2,2,3,2,1],#[-1,0,0,0,0,0],#[2,3,4,6,4,2],#[0,1,1,2,2,1],#[-2,-1,-2,-2,-1,0]]
def spanningCoefficients (i j : Fin 6) : ℤ := (spanningCoefficientsTable[i.val]!)[j.val]!
def selectedMultiples (i : Fin 6) : ℤ := #[1,0,2,0,1,2][i.val]!
theorem weight_lattice_spanning : ∀ i j : Fin 6,
    (∑ k : Fin 6, spanningCoefficients i k * CartanMatrix.E 6 k j) +
      selectedMultiples i * (Pi.single selectedNode 1 : Fin 6 → ℤ) j = (Pi.single i 1 : Fin 6 → ℤ) j := by decide +kernel

end Atlas.Chevalley.E6MinusculeTable
