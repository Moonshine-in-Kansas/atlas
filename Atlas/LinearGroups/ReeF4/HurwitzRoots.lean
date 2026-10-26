import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! The R1/R2 short-root labels in twice-integral quaternion coordinates.
These integers label basis vectors; they are never divided by two in the
characteristic-two coefficient field. -/
namespace Atlas.ReeF4

abbrev ShortRootLabel := Fin 3 × Fin 8
abbrev ScaledHurwitz := Fin 4 → ℤ

/-- Rows are the three octonion blocks. Columns are the source subscripts
-4,-3,-2,-1,1,2,3,4. Each tuple is twice its quaternion-coordinate root. -/
def scaledShortRoot (r : ShortRootLabel) : ScaledHurwitz :=
  (![![![2,0,0,0], ![0,2,0,0], ![0,0,2,0], ![0,0,0,2],
        ![0,0,0,-2], ![0,0,-2,0], ![0,-2,0,0], ![-2,0,0,0]],
     ![![1,1,1,-1], ![1,1,-1,1], ![1,-1,1,1], ![1,-1,-1,-1],
        ![-1,1,1,1], ![-1,1,-1,-1], ![-1,-1,1,-1], ![-1,-1,-1,1]],
     ![![1,1,1,1], ![1,1,-1,-1], ![1,-1,1,-1], ![-1,1,1,-1],
        ![1,-1,-1,1], ![-1,1,-1,1], ![-1,-1,1,1], ![-1,-1,-1,-1]]]) r.1 r.2

def rootDot (x y : ScaledHurwitz) : ℤ :=
  x 0*y 0 + x 1*y 1 + x 2*y 2 + x 3*y 3

/-- The R1 matrix, equivalently R2's quaternion map (1+i) z^j. -/
def rootPhi (x : ScaledHurwitz) : ScaledHurwitz :=
  ![x 0+x 1, x 0-x 1, x 2+x 3, x 2-x 3]

theorem rootPhi_square (x : ScaledHurwitz) : rootPhi (rootPhi x) = 2 • x := by
  funext i
  fin_cases i <;> simp [rootPhi] <;> ring

theorem rootPhi_norm (x : ScaledHurwitz) :
    rootDot (rootPhi x) (rootPhi x) = 2 * rootDot x x := by
  simp [rootPhi, rootDot]
  ring

theorem rootPhi_injective : Function.Injective rootPhi := by
  intro x y h
  have hh := congrArg rootPhi h
  rw [rootPhi_square, rootPhi_square] at hh
  funext i
  have hi := congrFun hh i
  change (2 : ℤ) * x i = 2 * y i at hi
  omega

theorem scaledShortRoot_norm : ∀ r : ShortRootLabel,
    rootDot (scaledShortRoot r) (scaledShortRoot r) = 4 := by decide

theorem scaledShortRoot_injective : Function.Injective scaledShortRoot := by decide

theorem scaledShortRoot_neg : ∀ r : ShortRootLabel,
    scaledShortRoot (r.1, Fin.rev r.2) = -scaledShortRoot r := by decide

-- The finite root system has 24 labels; this checks its small addition table.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem shortRoot_perpendicular_sum_exists : ∀ r s : ShortRootLabel,
    rootDot (scaledShortRoot r) (scaledShortRoot s) = 0 →
      ∃ t : ShortRootLabel, rootPhi (scaledShortRoot t) = scaledShortRoot r + scaledShortRoot s := by
  decide

theorem shortRoot_perpendicular_sum (r s : ShortRootLabel)
    (h : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0) :
    ∃! t : ShortRootLabel, rootPhi (scaledShortRoot t) = scaledShortRoot r + scaledShortRoot s := by
  obtain ⟨t, ht⟩ := shortRoot_perpendicular_sum_exists r s h
  exact ⟨t, ht, fun u hu => scaledShortRoot_injective (rootPhi_injective (hu.trans ht.symm))⟩

end Atlas.ReeF4
