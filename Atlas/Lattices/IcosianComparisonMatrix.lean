import Atlas.Lattices.IcosianRationalSpace

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

namespace Atlas.Lattices
open Atlas.Codes
open scoped Matrix

/-- A signed pair-Hadamard transform with the retained Golay coordinate marking. -/
def icosianComparisonData : Matrix (Fin 24) (Fin 24) ℚ :=
![![2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![2,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,-2,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,2,0,0,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,2,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,0,0,0,2,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,2],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,2,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,-2],
![0,0,0,0,0,0,0,0,2,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,2,0,-2,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,-2,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,-2,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,-2,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,-2,0,0,0,2,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,2,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0]]

def icosianLeechCoordinateIndex (p : Omega) : Fin 24 :=
  ⟨8*p.1.1.val+4*p.1.2.val+p.2.val, by
    have := p.1.1.isLt; have := p.1.2.isLt; have := p.2.isLt; omega⟩

def icosianRealCoordinateIndex (p : IcosianRealIndex) : Fin 24 :=
  ⟨8*p.1.val+2*p.2.1.val+p.2.2.val, by
    have := p.1.isLt; have := p.2.1.isLt; have := p.2.2.isLt; omega⟩

def icosianComparisonMatrix : Matrix Omega IcosianRealIndex ℚ := fun p q =>
  icosianComparisonData (icosianLeechCoordinateIndex p) (icosianRealCoordinateIndex q)

def icosianComparisonInverseMatrix : Matrix IcosianRealIndex Omega ℚ :=
  (1/8 : ℚ) • icosianComparisonMatrix.transpose

theorem icosianComparison_matrix_inverse :
    icosianComparisonMatrix * icosianComparisonInverseMatrix = 1 := by
  decide +kernel

theorem icosianComparison_inverse_matrix :
    icosianComparisonInverseMatrix * icosianComparisonMatrix = 1 := by
  decide +kernel

theorem icosianComparison_matrix_gram :
    icosianComparisonMatrix.transpose * icosianComparisonMatrix = (8 : ℚ) • 1 := by
  decide +kernel

end Atlas.Lattices
