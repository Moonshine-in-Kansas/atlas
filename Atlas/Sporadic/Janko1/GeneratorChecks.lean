import Atlas.Sporadic.Janko1.GeneratorMatrices

/-! Kernel checks of the small coordinate operators; no enumeration of J₁. -/
namespace Atlas.Janko1

def generatorExponent : Fin 4 → ℕ := ![7,3,2,2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- The four operators are checked on 64 pairs of the installed octonion basis.
private theorem generator_basis_mul : ∀ g : Fin 4, ∀ i j : Fin 8,
    generatorLinear g (SplitOctonion.mul (SplitOctonion.basisVector i)
      (SplitOctonion.basisVector j)) =
    SplitOctonion.mul (generatorLinear g (SplitOctonion.basisVector i))
      (generatorLinear g (SplitOctonion.basisVector j)) := by decide

theorem generatorLinear_mul (g : Fin 4) (x y : SplitOctonion.Carrier Field) :
    generatorLinear g (SplitOctonion.mul x y) =
      SplitOctonion.mul (generatorLinear g x) (generatorLinear g y) :=
  SplitOctonion.map_mul_of_basis (generatorLinear g) (generator_basis_mul g) x y

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- At most seven applications, tested on eight basis vectors for each operator.
private theorem generator_basis_pow : ∀ g : Fin 4, ∀ i : Fin 8,
    ((generatorLinear g) ^ generatorExponent g) (SplitOctonion.basisVector i) =
      SplitOctonion.basisVector i := by decide

theorem generatorLinear_pow (g : Fin 4) :
    (generatorLinear g) ^ generatorExponent g = 1 := by
  apply SplitOctonion.linearMap_ext
  exact generator_basis_pow g

end Atlas.Janko1
