import Atlas.Comparisons.Exceptional.E6.BinaryOrthogonal

/-! A marked binary Witt chart: two hyperbolic planes and an anisotropic plane.
These identities concern the actual E6 polynomial, not a group-order recognition. -/
namespace Atlas.Comparisons.E6Lattice
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def binaryChart (x : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  ![x 0+x 1+x 3+x 4+x 5, x 2+x 3, x 0+x 4,
    x 1+x 5, x 2+x 3+x 4, x 5]

def binaryChartInverse (y : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  ![y 1+y 2+y 4, y 3+y 5, y 0+y 1+y 2+y 3,
    y 0+y 2+y 3, y 1+y 4, y 5]

theorem binaryChart_left_inv : Function.LeftInverse binaryChartInverse binaryChart := by
  decide

theorem binaryChart_right_inv : Function.RightInverse binaryChartInverse binaryChart := by
  decide

def binaryChartLinearEquiv : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun := binaryChart
  invFun := binaryChartInverse
  left_inv := binaryChart_left_inv
  right_inv := binaryChart_right_inv
  map_add' x y := by
    funext i
    fin_cases i <;> simp [binaryChart] <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp [binaryChart] <;> ring

/-- Two hyperbolic pairs followed by the binary anisotropic plane. -/
def binaryWittForm : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2) :=
  QuadraticMap.proj 0 1 + QuadraticMap.proj 2 3 +
    QuadraticMap.proj 4 4 + QuadraticMap.proj 4 5 + QuadraticMap.proj 5 5

@[simp] theorem binaryWittForm_apply (x : Fin 6 → ZMod 2) :
    binaryWittForm x = x 0*x 1+x 2*x 3+x 4^2+x 4*x 5+x 5^2 := by
  simp [binaryWittForm, pow_two]

theorem binaryChart_form (x : Fin 6 → ZMod 2) :
    norm (binaryChart x) = x 0*x 1+x 2*x 3+x 4^2+x 4*x 5+x 5^2 := by
  revert x
  decide

/-- An actual isometry, with its marked inverse. -/
def binaryWittIsometry : binaryWittForm.IsometryEquiv (form (ZMod 2)) where
  toLinearEquiv := binaryChartLinearEquiv
  map_app' x := by
    change form (ZMod 2) (binaryChart x) = binaryWittForm x
    rw [form_apply, binaryChart_form, binaryWittForm_apply]

theorem binary_anisotropic_plane (a b : ZMod 2) :
    a^2+a*b+b^2 = 0 ↔ a = 0 ∧ b = 0 := by
  revert a b
  decide

end Atlas.Comparisons.E6Lattice
