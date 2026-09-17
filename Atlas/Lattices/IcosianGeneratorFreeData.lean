import Atlas.Lattices.IcosianComparisonSourceMembership
import Atlas.Lattices.IcosianGlueFreeCoordinates

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped Matrix QuadraticAlgebra BigOperators

/-- The twelve binary information positions, grouped into six F4 coefficients. -/
def icosianGlueFreePosition : Fin 12 → Fin 24 := ![10,11,14,15,16,17,18,19,20,21,22,23]

def icosianGlueRowIndex (k : Fin 12) : Fin 36 := ⟨24+k.val,by omega⟩

theorem icosianGlueRows_free : ∀ k l : Fin 12,
    icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition l) =
      if k=l then 1 else 0 := by
  decide +kernel

theorem icosianGlueRows_mem : ∀ k : Fin 12,
    (fun i => icosianMatrixFromCoefficients
      (fun j => goldenModuloTwo (icosianComparisonSourceCoefficients (icosianGlueRowIndex k) i j)))
      ∈ icosianMatrixGlue GoldenFour := by
  intro k
  have h := (icosianLeechModule_matrix_glue _).mp
    (icosianComparisonSourceGenerator_mem (icosianGlueRowIndex k))
  simpa only [icosianComparisonSourceGenerator,icosianModuloTwo_synthesis] using h

end Atlas.Lattices
