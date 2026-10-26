import Atlas.Algebra.Albert.Coordinates
import Mathlib.Tactic

/-! The uniform seven-parameter central translation formula. Its identification
with the already constructed Albert root groups is a separate bridge. -/
namespace Atlas.F4
variable {R : Type*} [CommRing R]

def centralSevenApply (p : Fin 7 → R) (x : Atlas.Albert.Carrier R) : Atlas.Albert.Carrier R :=
  (![x.1 0 - p 6 * x.2 2 7,x.1 1 + p 6 * x.2 2 7,x.1 2],
    ![![x.2 0 0 - p 0 * x.2 0 6 - p 2 * x.2 0 5 - p 5 * x.2 0 4 - p 6 * x.2 1 3,
        x.2 0 1 + p 0 * x.2 0 7 - p 3 * x.2 0 4 + p 4 * x.2 0 5 + p 6 * x.2 1 5,
        x.2 0 2 + p 1 * x.2 0 4 + p 2 * x.2 0 7 - p 4 * x.2 0 6 - p 6 * x.2 1 6,
        x.2 0 3 - p 1 * x.2 0 5 + p 3 * x.2 0 6 + p 5 * x.2 0 7 - p 6 * x.2 1 7,
        x.2 0 4,
        x.2 0 5,
        x.2 0 6,
        x.2 0 7],
      ![x.2 1 0 - p 0 * x.2 1 6 - p 2 * x.2 1 5 + p 4 * x.2 1 3 + p 6 * x.2 0 4,
        x.2 1 1 + p 0 * x.2 1 7 + p 3 * x.2 1 3 + p 5 * x.2 1 5 + p 6 * x.2 0 5,
        x.2 1 2 - p 1 * x.2 1 3 + p 2 * x.2 1 7 - p 5 * x.2 1 6 - p 6 * x.2 0 6,
        x.2 1 3,
        x.2 1 4 + p 1 * x.2 1 5 - p 3 * x.2 1 6 - p 4 * x.2 1 7 + p 6 * x.2 0 7,
        x.2 1 5,
        x.2 1 6,
        x.2 1 7],
      ![x.2 2 0 - p 0 * x.2 2 6 + p 1 * x.2 2 1 - p 2 * x.2 2 5 + p 3 * x.2 2 2 - p 4 * x.2 2 4 + p 5 * x.2 2 3 + p 6 * x.1 0 - p 6 * x.1 1 + (p 0*p 1+p 2*p 3+p 4*p 5-(p 6)^2)*x.2 2 7,
        x.2 2 1 + p 0 * x.2 2 7,
        x.2 2 2 + p 2 * x.2 2 7,
        x.2 2 3 + p 4 * x.2 2 7,
        x.2 2 4 - p 5 * x.2 2 7,
        x.2 2 5 - p 3 * x.2 2 7,
        x.2 2 6 - p 1 * x.2 2 7,
        x.2 2 7]])

theorem centralSevenApply_zero (x : Atlas.Albert.Carrier R) : centralSevenApply 0 x=x := by
  apply Prod.ext
  · ext i; fin_cases i <;> simp [centralSevenApply,Matrix.vecHead,Matrix.vecTail]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [centralSevenApply,Matrix.vecHead,Matrix.vecTail]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
/-- Exact additive composition law, without dividing by two. -/
theorem centralSevenApply_add (p q : Fin 7 → R) (x : Atlas.Albert.Carrier R) :
    centralSevenApply p (centralSevenApply q x)=centralSevenApply (p+q) x := by
  apply Prod.ext
  · ext i; fin_cases i <;> simp [centralSevenApply,Matrix.vecHead,Matrix.vecTail] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [centralSevenApply,Matrix.vecHead,Matrix.vecTail] <;> ring

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
def centralSevenLinear (p : Fin 7 → R) : Atlas.Albert.Carrier R →ₗ[R] Atlas.Albert.Carrier R where
  toFun := centralSevenApply p
  map_add' x y := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [centralSevenApply,Matrix.vecHead,Matrix.vecTail] <;> ring
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [centralSevenApply,Matrix.vecHead,Matrix.vecTail] <;> ring
  map_smul' t x := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [centralSevenApply,Matrix.vecHead,Matrix.vecTail] <;> ring
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [centralSevenApply,Matrix.vecHead,Matrix.vecTail] <;> ring

def centralSevenEquiv (p : Fin 7 → R) : Atlas.Albert.Carrier R ≃ₗ[R] Atlas.Albert.Carrier R where
  toLinearMap := centralSevenLinear p
  invFun := centralSevenApply (-p)
  left_inv x := by
    change centralSevenApply (-p) (centralSevenApply p x)=x
    rw [centralSevenApply_add,neg_add_cancel,centralSevenApply_zero]
  right_inv x := by
    change centralSevenApply p (centralSevenApply (-p) x)=x
    rw [centralSevenApply_add,add_neg_cancel,centralSevenApply_zero]

/-- The eight negative-weight spin coordinates used by the big cell. -/
def negativeSpinCoordinates (x : Atlas.Albert.Carrier R) : Fin 8 → R :=
  ![x.2 0 4,x.2 0 5,x.2 0 6,x.2 0 7,x.2 1 3,x.2 1 5,x.2 1 6,x.2 1 7]

theorem centralSeven_negative (p : Fin 7 → R) (x : Atlas.Albert.Carrier R) :
    negativeSpinCoordinates (centralSevenApply p x)=negativeSpinCoordinates x := by
  ext i; fin_cases i <;> rfl

theorem centralSeven_C7 (p : Fin 7 → R) (x : Atlas.Albert.Carrier R) :
    (centralSevenApply p x).2 2 7=x.2 2 7 := rfl

/-- Coordinates translated independently on the C₇=1 chart. -/
def centralSevenCoordinates (x : Atlas.Albert.Carrier R) : Fin 7 → R :=
  ![x.2 2 1,-x.2 2 6,x.2 2 2,-x.2 2 5,x.2 2 3,-x.2 2 4,-x.1 0]

theorem centralSeven_coordinates (p : Fin 7 → R) (x : Atlas.Albert.Carrier R) :
    centralSevenCoordinates (centralSevenApply p x)=
      centralSevenCoordinates x + x.2 2 7 • p := by
  ext i
  fin_cases i <;> simp [centralSevenCoordinates,centralSevenApply,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem centralSeven_coordinates_chart (p : Fin 7 → R) (x : Atlas.Albert.Carrier R)
    (hx : x.2 2 7=1) :
    centralSevenCoordinates (centralSevenApply p x)=centralSevenCoordinates x+p := by
  rw [centralSeven_coordinates,hx,one_smul]

theorem centralSevenEquiv_injective : Function.Injective (centralSevenEquiv (R := R)) := by
  intro p q h
  let x : Atlas.Albert.Carrier R := (0,![0,0,![0,0,0,0,0,0,0,1]])
  have hx : x.2 2 7=1 := rfl
  have he := congrArg (fun g : Atlas.Albert.Carrier R ≃ₗ[R] Atlas.Albert.Carrier R =>
    centralSevenCoordinates (g x)) h
  change centralSevenCoordinates (centralSevenApply p x)=
    centralSevenCoordinates (centralSevenApply q x) at he
  rw [centralSeven_coordinates_chart p x hx,centralSeven_coordinates_chart q x hx] at he
  exact add_left_cancel he

end Atlas.F4
