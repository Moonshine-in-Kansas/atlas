import Atlas.LinearGroups.F4.ShortRadicalLayer
import Atlas.LinearGroups.F4.CentralSevenFormula

/-! The actual bilinear middle-layer displacement of the eight half roots.
These formulas are uniform over every field, including characteristic two. -/
namespace Atlas.F4
variable {R : Type*} [CommRing R]

/-- Middle-layer displacements, with the signs of the existing half-root parameters. -/
def halfRootCentralApply (i : Fin 8) (z : Fin 8 → R) : Fin 7 → R :=
  ![![z 1,0,-z 2,0,-z 3,0,-z 7],
    ![-z 0,0,0,-z 3,0,z 2,-z 6],
    ![0,-z 3,z 0,0,0,-z 1,z 5],
    ![0,z 2,0,z 1,z 0,0,-z 4],
    ![-z 5,0,z 6,0,0,z 7,0],
    ![z 4,0,0,-z 7,z 6,0,0],
    ![0,-z 7,-z 4,0,-z 5,0,0],
    ![0,z 6,0,z 5,0,-z 4,0]] i

def halfRootCentralLinear (i : Fin 8) : (Fin 8 → R) →ₗ[R] (Fin 7 → R) where
  toFun := halfRootCentralApply i
  map_add' x y := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [halfRootCentralApply] <;> ring
  map_smul' t x := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [halfRootCentralApply] <;> ring

/-- The diagonal coefficient vanishes; there is no self-interaction term. -/
theorem halfRootCentralApply_single_self (i : Fin 8) (t : R) :
    halfRootCentralApply i (Pi.single i t)=0 := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [halfRootCentralApply,Pi.single_apply]

variable {F : Type*} [Field F]

private theorem halfCentral_symm_mul_apply
    (a b : Atlas.Albert.Carrier F ≃ₗ[F] Atlas.Albert.Carrier F)
    (x : Atlas.Albert.Carrier F) : (a*b).symm x=b.symm (a.symm x) := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
/-- Exact first-degree displacement; the quadratic root term has zero middle projection. -/
theorem halfRoot_central (i : Fin 8) (t : F) (x : Atlas.Albert.Carrier F) :
    centralSevenCoordinates ((halfRoot i t).val x)=centralSevenCoordinates x+
      t • halfRootCentralApply i (oppositeLowerCoordinates x) := by
  unfold halfRoot
  rw [shortRoot_polynomial_all]
  fin_cases i
  all_goals
    ext j
    fin_cases j <;>
      simp [centralSevenCoordinates,halfRootCentralApply,oppositeLowerCoordinates,
        halfRootIndex,halfRootSign,shortRootL,shortRootQ,shortRootPosition,
        cycleCoefficient,shortRootFirstCoefficient,shortRootQuadraticLinear,shortRootQuadraticApply,
        Atlas.Albert.shortRootLinear,Atlas.Albert.shortRootFormula,Atlas.Albert.coordinateCycleEquiv,
        Atlas.Albert.coordinateCycle,Atlas.SplitOctonion.mul,Atlas.SplitOctonion.conjugate,
        Atlas.SplitOctonion.trace,Atlas.SplitOctonion.unit,Atlas.SplitOctonion.basisVector,
        Matrix.vecHead,Matrix.vecTail,LinearEquiv.mul_apply,halfCentral_symm_mul_apply,pow_succ] <;> ring

end Atlas.F4
