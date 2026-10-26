import Atlas.Sporadic.Janko1.Imaginary
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Four prescribed coordinate operators. Membership in the octonion
multiplication stabilizer is a separate proof, not an assumption. -/
namespace Atlas.Janko1

def imaginaryGeneratorMatrix (g : Fin 4) (i j : Fin 7) : Field :=
  match g with
  | 0 => if i = j+1 then 1 else 0
  | 1 => if i = 2*j then 1 else 0
  | 2 => if i = j then (if j = 0 ∨ j = 3 ∨ j = 5 ∨ j = 6 then -1 else 1) else 0
  | _ => if i+j = 0 then -2 else if i+j = 1 ∨ i+j = 2 ∨ i+j = 4 then 1 else 3

def generatorMatrix (g : Fin 4) : Matrix (Fin 8) (Fin 8) Field :=
  Fin.cases (Fin.cases 1 (fun _ => 0))
    (fun i => Fin.cases 0 (fun j => imaginaryGeneratorMatrix g i j))

def generatorCoordinates (g : Fin 4) : (Fin 8 → Field) →ₗ[Field] (Fin 8 → Field) :=
  Matrix.toLin' (generatorMatrix g)

def generatorLinear (g : Fin 4) : SplitOctonion.Carrier Field →ₗ[Field]
    SplitOctonion.Carrier Field :=
  wilsonEquiv.toLinearMap.comp ((generatorCoordinates g).comp wilsonEquiv.symm.toLinearMap)

theorem generatorLinear_coordinates (g : Fin 4) (x : Fin 8 → Field) :
    generatorLinear g (wilsonEquiv x) = wilsonEquiv (generatorCoordinates g x) := by
  simp [generatorLinear]

end Atlas.Janko1
