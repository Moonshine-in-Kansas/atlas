import Atlas.LinearGroups.Chevalley.TwistedE6.DiagramLattice
import Atlas.Comparisons.Exceptional.E6.RootRepresentatives

/-! The diagram on the inherited 36 positive integral root representatives.
Every finite assertion below is a small kernel-checked computation on that
existing list. It is not a certificate for a finite group or its order. -/
namespace Atlas.Chevalley.TwistedE6
open Atlas.Comparisons.E6Lattice

/-- Explicit action on the previously proved positive-root representatives. -/
def positiveDiagram : Equiv.Perm (Fin 36) where
  toFun := ![0,20,10,21,4,5,11,12,22,23,2,6,7,13,14,24,25,17,
    28,31,1,3,8,9,15,16,26,27,18,29,32,19,30,33,34,35]
  invFun := ![0,20,10,21,4,5,11,12,22,23,2,6,7,13,14,24,25,17,
    28,31,1,3,8,9,15,16,26,27,18,29,32,19,30,33,34,35]
  left_inv := by decide
  right_inv := by decide

theorem positiveDiagram_involutive : Function.Involutive positiveDiagram := by
  intro i
  fin_cases i <;> rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem latticeDiagram_rootRepresentative (i : Fin 36) :
    latticeDiagram ℤ (rootRepresentative i) = rootRepresentative (positiveDiagram i) := by
  revert i
  decide

set_option maxRecDepth 8192 in
theorem positiveDiagram_fixed_count :
    Fintype.card {i : Fin 36 // positiveDiagram i = i} = 12 := by decide

set_option maxRecDepth 8192 in
theorem positiveDiagram_moved_count :
    Fintype.card {i : Fin 36 // positiveDiagram i ≠ i} = 24 := by decide

set_option maxRecDepth 8192 in
theorem positiveDiagram_pair_count :
    Fintype.card {i : Fin 36 // i < positiveDiagram i} = 12 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem rootRepresentative_diagram_orthogonal (i : Fin 36)
    (hi : positiveDiagram i ≠ i) :
    (form ℤ).polarBilin (rootRepresentative i)
      (rootRepresentative (positiveDiagram i)) = 0 := by
  revert i
  decide

end Atlas.Chevalley.TwistedE6
