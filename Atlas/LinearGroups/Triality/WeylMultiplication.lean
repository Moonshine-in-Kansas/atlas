import Atlas.LinearGroups.Triality.WeylDistinct

/-! Left multiplication of the twelve actual Weyl representatives.
The finite index/sign table is proved on the actual eight-dimensional actions. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal

def weylLeftIndex (s : Bool) : Fin 12 → Fin 12 :=
  if s then ![1,0,3,2,5,4,7,6,9,8,11,10]
  else ![2,4,0,6,1,8,3,10,5,11,7,9]

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def weylLeftTorus (s : Bool) : Fin 12 → Kˣ × Fˣ :=
  if s then ![(1,1),(-1,1),(1,1),(-1,-1),(1,1),(1,-1),(1,1),(1,-1),(1,1),(-1,-1),(1,1),(-1,1)]
  else ![(1,1),(1,1),(1,-1),(1,1),(-1,-1),(1,1),(-1,1),(1,1),(-1,1),(1,1),(-1,-1),(1,-1)]

set_option maxHeartbeats 8000000 in
-- Twenty-four products, checked on eight coordinates in every characteristic.
theorem weylLeft_mul (s : Bool) (w : Fin 12) :
    (if s then shortWeyl F K else longWeyl F K) * weylLift F K w =
      weylLift F K (weylLeftIndex s w) * torusMap F K (weylLeftTorus F K s w) := by
  cases s <;> fin_cases w
  all_goals
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    ext i
    rcases i with i|i <;> fin_cases i <;>
      simp [weylLift, weylWord, weylLeftIndex, weylLeftTorus,
        Subgroup.coe_mul, LinearEquiv.mul_apply, shortWeyl_apply, longWeyl_apply,
        torusMap, torusWeights, diagonalEmbedding, diagonalLinear, sigmaUnit, baseUnit]

end Atlas.Triality
