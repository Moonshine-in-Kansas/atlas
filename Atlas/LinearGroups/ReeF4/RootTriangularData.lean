import Atlas.LinearGroups.ReeF4.WeylCoordinateTransport
import Atlas.LinearGroups.ReeF4.RootGroupCoordinates
import Atlas.LinearGroups.ReeF4.WeylSL2Parameters

/-! Finite support statements for the actual root formulas.
The fixed Weyl-prefix cases are checked in separate serial modules.
The grading is Wilson's absolute A grading, with zero on scalar coordinates. -/
namespace Atlas.ReeF4
open Atlas.Albert

def absoluteCoordinateGrade (c : WeylCoordinate) : ℤ :=
  (![![-12,-6,-4,-2,0,2,4,6,12],
      ![-10,-9,-7,-1,0,1,7,9,10],
      ![-11,-8,-5,3,0,-3,5,8,11]] : Fin 3 → Fin 9 → ℤ) c.1 c.2

def alternatingShortPermutation (k : Fin 4) : Equiv.Perm WeylCoordinate :=
  (weylRhoPermutation * weylSigmaPermutation)^k.val

def alternatingLongPermutation (k : Fin 4) : Equiv.Perm WeylCoordinate :=
  alternatingShortPermutation k * weylRhoPermutation

/-- The unchanged coordinate assertion which detects strict lowering support.
The permutation records transport of source and target coordinates simultaneously. -/
def StrictlyLoweringFormula {F : Type*} [CommRing F]
    (p : Equiv.Perm WeylCoordinate) (f : Carrier F → Carrier F) : Prop :=
  ∀ (w : Carrier F) (c : WeylCoordinate),
    (∀ d : WeylCoordinate, absoluteCoordinateGrade (p c) < absoluteCoordinateGrade (p d) →
      wilsonCoordinatesEquiv w d.1 d.2 = 0) →
    wilsonCoordinatesEquiv (f w) c.1 c.2 = wilsonCoordinatesEquiv w c.1 c.2

variable {F : Type*} [CommRing F] [CharP F 2]


end Atlas.ReeF4
