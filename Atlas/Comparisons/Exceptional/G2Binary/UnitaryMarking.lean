import Atlas.Comparisons.Exceptional.G2Binary.FieldNine
import Atlas.LinearGroups.Unitary.Hermitian

/-! A finite coordinate chart for the unitary side of the 28-point bridge.
All displayed coordinates and action entries below are verified in Lean;
the discovery JSON and Ruby search are not proof dependencies. -/
namespace Atlas.Comparisons.G2Binary
abbrev UVector := Fin 3 → FieldNine

def explicitHermitian (x y : UVector) : FieldNine := ∑ i, x i * (y i)^3

theorem explicitHermitian_eq (x y : UVector) :
    explicitHermitian x y = Atlas.Unitary.hermitian BaseThree FieldNine x y := by
  simp only [explicitHermitian, Atlas.Unitary.hermitian, fieldNine_conjugation]

def unitaryVector (i : Fin 28) : UVector :=
  ![![fieldNineLabel 0,fieldNineLabel 1,fieldNineLabel 4],
    ![fieldNineLabel 0,fieldNineLabel 1,fieldNineLabel 5],
    ![fieldNineLabel 0,fieldNineLabel 1,fieldNineLabel 7],
    ![fieldNineLabel 0,fieldNineLabel 1,fieldNineLabel 8],
    ![fieldNineLabel 1,fieldNineLabel 0,fieldNineLabel 4],
    ![fieldNineLabel 1,fieldNineLabel 0,fieldNineLabel 5],
    ![fieldNineLabel 1,fieldNineLabel 0,fieldNineLabel 7],
    ![fieldNineLabel 1,fieldNineLabel 0,fieldNineLabel 8],
    ![fieldNineLabel 1,fieldNineLabel 1,fieldNineLabel 1],
    ![fieldNineLabel 1,fieldNineLabel 1,fieldNineLabel 2],
    ![fieldNineLabel 1,fieldNineLabel 1,fieldNineLabel 3],
    ![fieldNineLabel 1,fieldNineLabel 1,fieldNineLabel 6],
    ![fieldNineLabel 1,fieldNineLabel 2,fieldNineLabel 1],
    ![fieldNineLabel 1,fieldNineLabel 2,fieldNineLabel 2],
    ![fieldNineLabel 1,fieldNineLabel 2,fieldNineLabel 3],
    ![fieldNineLabel 1,fieldNineLabel 2,fieldNineLabel 6],
    ![fieldNineLabel 1,fieldNineLabel 3,fieldNineLabel 1],
    ![fieldNineLabel 1,fieldNineLabel 3,fieldNineLabel 2],
    ![fieldNineLabel 1,fieldNineLabel 3,fieldNineLabel 3],
    ![fieldNineLabel 1,fieldNineLabel 3,fieldNineLabel 6],
    ![fieldNineLabel 1,fieldNineLabel 4,fieldNineLabel 0],
    ![fieldNineLabel 1,fieldNineLabel 5,fieldNineLabel 0],
    ![fieldNineLabel 1,fieldNineLabel 6,fieldNineLabel 1],
    ![fieldNineLabel 1,fieldNineLabel 6,fieldNineLabel 2],
    ![fieldNineLabel 1,fieldNineLabel 6,fieldNineLabel 3],
    ![fieldNineLabel 1,fieldNineLabel 6,fieldNineLabel 6],
    ![fieldNineLabel 1,fieldNineLabel 7,fieldNineLabel 0],
    ![fieldNineLabel 1,fieldNineLabel 8,fieldNineLabel 0]] i

def unitaryRootImage (i j : Fin 28) : Fin 28 :=
  ![![0,3,1,2,23,11,14,16,27,6,25,12,5,20,9,18,24,8,26,4,22,10,13,19,7,21,15,17],
    ![3,1,0,2,13,25,18,8,14,22,27,4,17,11,7,20,5,26,23,10,24,9,21,6,15,16,12,19],
    ![1,3,2,0,9,19,24,12,23,15,7,27,10,16,20,4,26,6,11,22,25,8,5,21,17,14,13,18],
    ![1,2,0,3,17,15,10,22,5,27,13,24,20,6,19,8,9,25,7,26,23,11,18,12,21,4,14,16],
    ![19,11,15,25,4,7,5,6,26,2,16,13,21,1,22,9,20,3,12,23,10,18,27,0,8,17,24,14],
    ![12,16,22,8,7,5,4,6,15,18,26,0,11,24,21,3,25,14,20,2,9,17,19,10,27,1,23,13],
    ![9,23,17,13,5,7,6,4,19,14,3,26,25,10,0,21,15,24,1,20,8,16,11,18,2,27,22,12],
    ![24,14,10,18,5,6,4,7,1,26,12,17,2,21,8,23,0,20,22,13,11,19,3,27,16,9,25,15],
    ![27,7,23,15,26,3,19,14,8,10,11,9,16,25,1,5,22,0,13,20,6,2,12,21,4,18,24,17],
    ![14,22,4,27,15,18,0,26,11,9,8,10,24,17,6,2,3,23,20,12,5,1,21,13,19,7,25,16],
    ![25,27,12,6,16,26,13,2,11,8,10,9,7,3,18,22,20,15,24,1,4,0,17,5,14,21,23,19],
    ![5,13,27,24,1,12,26,17,9,10,8,11,0,4,23,19,14,20,2,25,7,3,6,16,21,15,22,18],
    ![11,17,7,20,21,0,25,10,22,19,2,5,12,14,15,13,8,26,4,24,23,18,16,3,9,27,1,6],
    ![20,4,16,10,11,24,3,21,18,23,6,1,15,13,12,14,26,9,25,7,22,19,0,17,27,8,2,5],
    ![6,8,20,19,22,21,9,1,7,0,24,16,15,12,14,13,23,5,10,26,25,17,27,11,18,2,3,4],
    ![18,20,9,5,2,8,21,23,3,4,17,25,13,14,12,15,6,22,26,11,24,16,10,27,1,19,0,7],
    ![7,25,26,9,20,1,15,24,22,27,4,14,8,2,23,21,16,18,19,17,10,6,12,11,0,5,13,3],
    ![8,26,24,4,25,14,2,20,27,23,15,7,1,9,21,22,19,17,16,18,11,5,10,13,6,3,12,0],
    ![26,6,11,22,12,20,23,3,13,5,24,27,21,25,10,0,19,16,18,17,9,4,7,1,14,8,15,2],
    ![23,10,5,26,0,22,20,13,6,12,27,25,24,21,3,11,17,18,16,19,8,7,2,4,9,15,14,1],
    ![22,24,25,23,16,18,19,17,6,5,4,7,3,0,2,1,10,11,9,8,20,27,13,12,15,14,21,26],
    ![10,9,8,11,12,14,15,13,23,22,25,24,18,19,17,16,6,5,4,7,27,21,1,2,3,0,20,26],
    ![13,21,19,7,27,2,11,18,12,1,17,26,16,20,4,10,8,15,3,5,0,9,22,24,25,23,6,14],
    ![4,18,21,12,19,10,1,27,2,13,26,16,20,17,11,7,14,9,6,0,3,8,25,23,22,24,5,15],
    ![16,15,6,21,8,27,17,0,26,19,14,3,9,5,18,20,7,2,10,12,1,11,25,22,24,23,4,13],
    ![21,5,14,17,3,16,27,9,18,26,0,15,6,8,20,19,1,4,13,11,2,10,23,24,22,25,7,12],
    ![15,12,13,14,8,10,11,9,24,25,23,22,17,16,19,18,2,1,0,3,21,27,6,5,4,7,26,20],
    ![17,19,18,16,22,24,25,23,0,3,1,2,6,5,4,7,9,8,11,10,21,26,14,15,13,12,20,27]] i j

def unitaryRootAction (i : Fin 28) (x : UVector) : UVector :=
  x + (imaginaryUnit * explicitHermitian x (unitaryVector i)) • unitaryVector i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Only 28 displayed vectors and nine scalars are checked.
theorem unitary_marking_geometry :
    (∀ i : Fin 28, unitaryVector i ≠ 0 ∧
      explicitHermitian (unitaryVector i) (unitaryVector i) = 0) ∧
    (∀ i j : Fin 28, ∀ a : FieldNine, a ≠ 0 →
      unitaryVector i = a • unitaryVector j → i = j) ∧
    (∀ a : FieldNine, a + a^3 = 0 → a = 0 ∨ a = imaginaryUnit ∨ a = -imaginaryUnit) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Check each transvection on the 28 marked projective representatives.
theorem unitary_root_action_checked : ∀ i j : Fin 28,
    ∃ a : FieldNine, a ≠ 0 ∧
      unitaryRootAction i (unitaryVector j) = a • unitaryVector (unitaryRootImage i j) := by decide

end Atlas.Comparisons.G2Binary
