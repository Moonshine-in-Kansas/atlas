import Atlas.Comparisons.Exceptional.E6.TernaryReduction
import Atlas.LinearGroups.Orthogonal.Basic

/-! Explicit marked coordinates for the five-dimensional ternary quotient.
The retained B2 form is recovered up to the nonzero scale two. -/
namespace Atlas.Comparisons.E6Lattice
open Atlas.Orthogonal

def ternaryChart (x : VectorB 2 (ZMod 3)) : Fin 5 → ZMod 3 :=
  let a := x.1 (.inl 0)
  let b := x.1 (.inr 0)
  let c := x.1 (.inl 1)
  let d := x.1 (.inr 1)
  let e := x.2
  ![c+2*d,b,a+2*c+d,2*a+d+e,2*b+c+d+e]

def ternaryChartInverse (y : Fin 5 → ZMod 3) : VectorB 2 (ZMod 3) :=
  (Sum.elim ![y 0+y 2,2*y 0+y 1+2*y 2+2*y 3+y 4]
    ![y 1,y 0+y 1+2*y 2+2*y 3+y 4],2*y 1+2*y 2+2*y 3+2*y 4)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Only 243 vectors in the full five-dimensional domain.
theorem ternaryChart_left_inv : Function.LeftInverse ternaryChartInverse ternaryChart := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Only 243 vectors in the full five-dimensional codomain.
theorem ternaryChart_right_inv : Function.RightInverse ternaryChartInverse ternaryChart := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Exact polynomial evaluation on the entire five-dimensional space.
theorem ternaryChart_form (x : VectorB 2 (ZMod 3)) :
    norm (quotientSection (ternaryChart x)) = 2 * formB 2 (ZMod 3) x := by
  revert x
  decide

def ternaryChartLinearEquiv : VectorB 2 (ZMod 3) ≃ₗ[ZMod 3] (Fin 5 → ZMod 3) where
  toFun := ternaryChart
  invFun := ternaryChartInverse
  left_inv := ternaryChart_left_inv
  right_inv := ternaryChart_right_inv
  map_add' x y := by
    funext i
    fin_cases i <;> simp [ternaryChart] <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp [ternaryChart] <;> ring

def quotientSectionLinear : (Fin 5 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3) where
  toFun := quotientSection
  map_add' x y := by funext i; fin_cases i <;> simp [quotientSection]
  map_smul' a x := by funext i; fin_cases i <;> simp [quotientSection]

def quotientForm : QuadraticForm (ZMod 3) (Fin 5 → ZMod 3) :=
  (form (ZMod 3)).comp quotientSectionLinear

/-- Actual isometry of quadratic spaces, with the nonzero scale stated explicitly. -/
def ternaryQuotientIsometry :
    ((2 : ZMod 3) • formB 2 (ZMod 3)).IsometryEquiv quotientForm where
  toLinearEquiv := ternaryChartLinearEquiv
  map_app' x := by
    change form (ZMod 3) (quotientSection (ternaryChart x)) = 2 * formB 2 (ZMod 3) x
    rw [form_apply]
    exact ternaryChart_form x

end Atlas.Comparisons.E6Lattice

