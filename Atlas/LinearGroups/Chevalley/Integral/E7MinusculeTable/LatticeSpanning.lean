import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Data

/-! E7 minuscule certificate component: LatticeSpanning. -/
namespace Atlas.Chevalley.E7MinusculeTable
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def spanningCoefficientsTable : Array (Array ℤ) := #[#[2,2,3,4,3,2,1],#[1,2,2,3,2,1,0],#[3,4,6,8,6,4,2],#[4,6,8,12,9,6,3],#[2,3,4,6,5,3,1],#[2,3,4,6,5,4,2],#[0,0,0,0,0,0,0]]
def spanningCoefficients (i j : Fin 7) : ℤ := (spanningCoefficientsTable[i.val]!)[j.val]!
def selectedMultiples (i : Fin 7) : ℤ := #[0,1,0,0,1,0,1][i.val]!
theorem weight_lattice_spanning : ∀ i j : Fin 7,
    (∑ k : Fin 7, spanningCoefficients i k * CartanMatrix.E 7 k j) +
      selectedMultiples i * (Pi.single selectedNode 1 : Fin 7 → ℤ) j = (Pi.single i 1 : Fin 7 → ℤ) j := by decide +kernel

end Atlas.Chevalley.E7MinusculeTable
