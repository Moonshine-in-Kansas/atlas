import Atlas.Comparisons.Exceptional.E6.Lattice

/-! The radical and an explicit five-coordinate quotient chart modulo three.
All finite checks range over the entire 3^6 coordinate space. -/
namespace Atlas.Comparisons.E6Lattice
open Matrix

def ternaryGram : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  gram.map (Int.castRingHom (ZMod 3))

def radicalVector (a : ZMod 3) : Fin 6 → ZMod 3 := ![a,-a,0,a,-a,0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction of the explicit 729 vectors, not a group enumeration.
theorem ternary_radical (x : Fin 6 → ZMod 3) :
    ternaryGram *ᵥ x = 0 ↔ ∃ a, x = radicalVector a := by
  revert x
  decide

def quotientCoordinates (x : Fin 6 → ZMod 3) : Fin 5 → ZMod 3 :=
  ![x 1+x 0,x 2,x 3-x 0,x 4+x 0,x 5]

def quotientSection (y : Fin 5 → ZMod 3) : Fin 6 → ZMod 3 :=
  ![0,y 0,y 1,y 2,y 3,y 4]

theorem quotient_section (y : Fin 5 → ZMod 3) :
    quotientCoordinates (quotientSection y) = y := by
  funext i
  fin_cases i <;> simp [quotientCoordinates,quotientSection]

theorem norm_quotient (x : Fin 6 → ZMod 3) :
    norm (quotientSection (quotientCoordinates x)) = norm x := by
  apply sub_eq_zero.mp
  simp [quotientSection,quotientCoordinates,norm]
  ring_nf
  simp only [show (3 : ZMod 3) = 0 by decide, mul_zero, add_zero, sub_zero]

theorem radical_norm (a : ZMod 3) : norm (radicalVector a) = 0 := by
  simp [norm,radicalVector]
  ring_nf
  simp only [show (6 : ZMod 3) = 0 by decide, mul_zero]

end Atlas.Comparisons.E6Lattice
