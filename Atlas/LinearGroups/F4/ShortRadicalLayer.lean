import Atlas.LinearGroups.F4.ParabolicShortRoots

/-! The eight degree-one short roots translate the negative-weight coordinates
of the opposite affine chart. This does not assert radical closure. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def oppositeLowerCoordinates (x : Carrier F) : Fin 8→F :=
  ![x.2 0 4,x.2 0 5,x.2 0 6,x.2 0 7,x.2 1 3,x.2 1 5,x.2 1 6,x.2 1 7]

def halfRootIndex : Fin 8→Fin 24 := ![8,9,10,12,16,17,18,19]
def halfRootSign : Fin 8→ℤ := ![1,1,-1,1,-1,1,-1,-1]

def halfRoot (i : Fin 8) (t : F) : Model F :=
  shortRoot (shortRootPosition (halfRootIndex i)).1
    (shortRootPosition (halfRootIndex i)).2 ((halfRootSign i : F)*t)

theorem halfRoot_parabolic (i : Fin 8) (t : F) : halfRoot i t∈parabolicPointStabilizer := by
  apply shortRoot_mem_parabolicPointStabilizer
  revert i
  decide +kernel

private theorem symm_mul_apply (a b : Carrier F ≃ₗ[F] Carrier F) (x : Carrier F) :
    (a*b).symm x=b.symm (a.symm x) := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
/-- Only nine lower coordinates are expanded, rather than the full group word. -/
theorem halfRoot_lower (i : Fin 8) (t : F) (x : Carrier F) :
    ((halfRoot i t).val x).2 2 7=x.2 2 7 ∧
      oppositeLowerCoordinates ((halfRoot i t).val x)=
        oppositeLowerCoordinates x+Pi.single i (t*x.2 2 7) := by
  unfold halfRoot
  rw [shortRoot_polynomial_all]
  fin_cases i
  all_goals
    constructor
    · simp [halfRootIndex,halfRootSign,shortRootL,shortRootQ,shortRootPosition,
        cycleCoefficient,shortRootFirstCoefficient,shortRootQuadraticLinear,shortRootQuadraticApply,
        shortRootLinear,shortRootFormula,coordinateCycleEquiv,Atlas.Albert.coordinateCycle,
        SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
        SplitOctonion.basisVector,Matrix.vecHead,Matrix.vecTail,LinearEquiv.mul_apply,symm_mul_apply,pow_succ]
    · ext j; fin_cases j <;>
        simp [oppositeLowerCoordinates,halfRootIndex,halfRootSign,shortRootL,shortRootQ,shortRootPosition,
          cycleCoefficient,shortRootFirstCoefficient,shortRootQuadraticLinear,shortRootQuadraticApply,
          shortRootLinear,shortRootFormula,coordinateCycleEquiv,Atlas.Albert.coordinateCycle,
          SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
          SplitOctonion.basisVector,Matrix.vecHead,Matrix.vecTail,LinearEquiv.mul_apply,symm_mul_apply,pow_succ,Pi.single_apply] <;> ring

end Atlas.F4
