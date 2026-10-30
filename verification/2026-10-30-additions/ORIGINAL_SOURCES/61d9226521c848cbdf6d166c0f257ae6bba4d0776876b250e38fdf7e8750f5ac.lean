import FamilyWork.PositiveCoordinates
import Atlas.LinearGroups.Chevalley.TwistedE6.PositiveRootOrbits
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise

/-! a height-ordered enumeration in diagram-orbit blocks.

The 24 block representatives are the smaller labels of the existing diagram
orbits, sorted by coordinate height with numerical label as the tie-breaker.
The explicit 36-label list is their concatenation, so a moved orbit occurs as
one adjacent pair and a fixed orbit as one singleton. All finite certificates
use ordinary `decide`; the actual-root height statement uses PositiveCoordinates.

Verification receipts are recorded separately. No assertion about a
group product, collection, or group order is made. -/

noncomputable section
namespace Atlas.Chevalley.TwistedE6
open Atlas.Comparisons.E6Lattice

/-- Coordinate-sum height of an existing positive representative. -/
def e6PositiveCoordinateHeight (i : Fin 36) : ℤ :=
  ∑ j : Fin 6, rootRepresentative i j

/-- A fixed label contributes one entry; a moved label contributes its whole orbit. -/
def e6PositiveOrbitBlock (i : Fin 36) : List (Fin 36) :=
  if positiveDiagram i = i then [i] else [i, positiveDiagram i]

/-- One representative of each diagram orbit, in nondecreasing height order. -/
def e6PositiveOrbitRepresentatives : List (Fin 36) :=
  [0, 1, 2, 4, 3, 5, 6, 7, 8, 13, 9, 14, 15, 16, 17, 26,
    18, 27, 19, 29, 30, 33, 34, 35]

/-- Explicit concatenation of the 24 diagram-orbit blocks. -/
def e6PositiveOrbitOrder : List (Fin 36) :=
  [0, 1, 20, 2, 10, 4, 3, 21, 5, 6, 11, 7, 12, 8, 22, 13,
    9, 23, 14, 15, 24, 16, 25, 17, 26, 18, 28, 27, 19, 31,
    29, 30, 32, 33, 34, 35]

theorem e6PositiveOrbitBlock_of_fixed (i : Fin 36) (hi : positiveDiagram i = i) :
    e6PositiveOrbitBlock i = [i] := by
  simp [e6PositiveOrbitBlock, hi]

theorem e6PositiveOrbitBlock_of_moved (i : Fin 36) (hi : positiveDiagram i ≠ i) :
    e6PositiveOrbitBlock i = [i, positiveDiagram i] := by
  simp [e6PositiveOrbitBlock, hi]

theorem mem_e6PositiveOrbitBlock (i j : Fin 36) :
    j ∈ e6PositiveOrbitBlock i ↔ j = i ∨ j = positiveDiagram i := by
  by_cases hi : positiveDiagram i = i <;> simp [e6PositiveOrbitBlock, hi]

/-- Each individual block is stable under the existing diagram involution. -/
theorem e6PositiveOrbitBlock_diagram_mem (i j : Fin 36)
    (hj : j ∈ e6PositiveOrbitBlock i) : positiveDiagram j ∈ e6PositiveOrbitBlock i := by
  rw [mem_e6PositiveOrbitBlock] at hj ⊢
  rcases hj with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (positiveDiagram_involutive i)

section FiniteCertificates

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem e6PositiveOrbitRepresentatives_length :
    e6PositiveOrbitRepresentatives.length = 24 := by decide

theorem e6PositiveOrbitRepresentatives_nodup :
    e6PositiveOrbitRepresentatives.Nodup := by decide

/-- Exactly the smaller member of every orbit is selected, including fixed labels. -/
theorem mem_e6PositiveOrbitRepresentatives_iff (i : Fin 36) :
    i ∈ e6PositiveOrbitRepresentatives ↔ i ≤ positiveDiagram i := by
  revert i
  decide

theorem e6PositiveOrbitOrder_length : e6PositiveOrbitOrder.length = 36 := by decide

theorem e6PositiveOrbitOrder_nodup : e6PositiveOrbitOrder.Nodup := by decide

theorem mem_e6PositiveOrbitOrder (i : Fin 36) : i ∈ e6PositiveOrbitOrder := by
  revert i
  decide

/-- This identity certifies that the orbit pairs are adjacent in the explicit order. -/
theorem e6PositiveOrbitOrder_eq_flatMap :
    e6PositiveOrbitOrder = e6PositiveOrbitRepresentatives.flatMap e6PositiveOrbitBlock := by
  decide

theorem e6PositiveCoordinateHeight_diagram (i : Fin 36) :
    e6PositiveCoordinateHeight (positiveDiagram i) = e6PositiveCoordinateHeight i := by
  revert i
  decide

theorem e6PositiveOrbitRepresentatives_pairwise_coordinateHeight :
    e6PositiveOrbitRepresentatives.Pairwise
      (fun i j => e6PositiveCoordinateHeight i ≤ e6PositiveCoordinateHeight j) := by
  decide

/-- All 36 labels are in nondecreasing coordinate height, including within each block. -/
theorem e6PositiveOrbitOrder_pairwise_coordinateHeight :
    e6PositiveOrbitOrder.Pairwise
      (fun i j => e6PositiveCoordinateHeight i ≤ e6PositiveCoordinateHeight j) := by
  decide

end FiniteCertificates

theorem e6PositiveOrbitBlock_coordinateHeight (i j : Fin 36)
    (hj : j ∈ e6PositiveOrbitBlock i) :
    e6PositiveCoordinateHeight j = e6PositiveCoordinateHeight i := by
  rcases (mem_e6PositiveOrbitBlock i j).mp hj with rfl | rfl
  · rfl
  · exact e6PositiveCoordinateHeight_diagram i

/-- The finite coordinate statistic is the height in the actual E6 base. -/
theorem e6PositiveRootEnumeration_height (i : Fin 36) :
    E6Data.base.height (e6PositiveRootEnumeration i).val = e6PositiveCoordinateHeight i := by
  rw [e6_height_eq_coordinate_sum]
  rfl

theorem e6PositiveOrbitOrder_pairwise_height :
    e6PositiveOrbitOrder.Pairwise (fun i j =>
      E6Data.base.height (e6PositiveRootEnumeration i).val ≤
        E6Data.base.height (e6PositiveRootEnumeration j).val) := by
  simpa only [e6PositiveRootEnumeration_height] using
    e6PositiveOrbitOrder_pairwise_coordinateHeight

/-- The same orbit-block order, now in the actual positive-root subtype. -/
def e6PositiveRootOrbitOrder : List {β : E6Data.Root // E6Data.base.IsPos β} :=
  e6PositiveOrbitOrder.map e6PositiveRootEnumeration

theorem e6PositiveRootOrbitOrder_length : e6PositiveRootOrbitOrder.length = 36 := by
  simp only [e6PositiveRootOrbitOrder, List.length_map, e6PositiveOrbitOrder_length]

theorem e6PositiveRootOrbitOrder_nodup : e6PositiveRootOrbitOrder.Nodup := by
  exact List.Nodup.map e6PositiveRootEnumeration_injective e6PositiveOrbitOrder_nodup

theorem mem_e6PositiveRootOrbitOrder (β : {β : E6Data.Root // E6Data.base.IsPos β}) :
    β ∈ e6PositiveRootOrbitOrder := by
  obtain ⟨i, rfl⟩ := e6PositiveRootEnumeration_surjective β
  exact List.mem_map.mpr ⟨i, mem_e6PositiveOrbitOrder i, rfl⟩

/-- An exhaustive, duplicate-free orbit-block order sorted by the actual base height. -/
theorem e6PositiveRootOrbitOrder_pairwise_height :
    e6PositiveRootOrbitOrder.Pairwise
      (fun β γ => E6Data.base.height β.val ≤ E6Data.base.height γ.val) := by
  simpa only [e6PositiveRootOrbitOrder, List.pairwise_map] using
    e6PositiveOrbitOrder_pairwise_height

end Atlas.Chevalley.TwistedE6
