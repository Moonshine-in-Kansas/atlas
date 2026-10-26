import Atlas.LinearGroups.F4.RootData
import Atlas.Algebra.Albert.Coordinates

/-! Integral combinatorial weights of the marked Albert coordinates.
These finite identities do not assert the existence or fullness of a torus. -/
namespace Atlas.F4.Weights
open Atlas.F4.RootData

/-- Slots zero, one, two are respectively A, B, C. -/
def slotWeight : Fin 3 → Fin 8 → RootData.Vector :=
  ![![![1,1,1,-1], ![1,1,-1,1], ![1,-1,1,1], ![1,-1,-1,-1],
       ![-1,1,1,1], ![-1,1,-1,-1], ![-1,-1,1,-1], ![-1,-1,-1,1]],
    ![![1,1,1,1], ![1,1,-1,-1], ![1,-1,1,-1], ![-1,1,1,-1],
       ![1,-1,-1,1], ![-1,1,-1,1], ![-1,-1,1,1], ![-1,-1,-1,-1]],
    ![![2,0,0,0], ![0,2,0,0], ![0,0,2,0], ![0,0,0,2],
       ![0,0,0,-2], ![0,0,-2,0], ![0,-2,0,0], ![-2,0,0,0]]]

def coordinateWeight : Atlas.Albert.Coordinate → RootData.Vector :=
  Sum.elim (fun _ => 0) (fun p => slotWeight p.1 p.2)

theorem diagonal_weight (i : Fin 3) : coordinateWeight (.inl i) = 0 := rfl

theorem octonion_weight (i : Fin 3) (j : Fin 8) :
    coordinateWeight (.inr (i,j)) = slotWeight i j := rfl

def slotRoot : Fin 3 × Fin 8 → Root :=
  fun p => (![![33,34,36,39,40,43,45,46],
             ![32,35,37,41,38,42,44,47],
             ![24,26,28,30,31,29,27,25]] : Fin 3 → Fin 8 → Root) p.1 p.2

theorem slotRoot_coordinates : ∀ p : Fin 3 × Fin 8,
    coordinates (slotRoot p) = slotWeight p.1 p.2 := by decide +kernel

theorem slotRoot_short : ∀ p : Fin 3 × Fin 8, IsShort (slotRoot p) := by decide +kernel

theorem slotRoot_injective : Function.Injective slotRoot := by decide +kernel

theorem every_short_root : ∀ r : Root, IsShort r → ∃ p : Fin 3 × Fin 8, slotRoot p = r := by
  decide +kernel

theorem opposite_weight : ∀ (i : Fin 3) (j : Fin 8),
    slotWeight i (7-j) = -slotWeight i j := by decide +kernel

/-- The actual integral split multiplication supplies the cubic support test. -/
def cubicCoefficient (i j k : Fin 8) : ℤ :=
  Atlas.SplitOctonion.trace (Atlas.SplitOctonion.mul
    (Atlas.SplitOctonion.mul (Atlas.SplitOctonion.basisVector i)
      (Atlas.SplitOctonion.basisVector j)) (Atlas.SplitOctonion.basisVector k))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Every nonzero octonion cubic monomial has total weight zero. -/
theorem cubic_support_weight_zero : ∀ (i j k : Fin 8), cubicCoefficient i j k ≠ 0 →
    slotWeight 0 i + slotWeight 1 j + slotWeight 2 k = 0 := by decide +kernel

/-- Each of the six shears in the coefficientwise existing G₂ root A has this weight. -/
theorem rootA_shear_weights : ∀ i : Fin 3,
    slotWeight i 0 - slotWeight i 6 = coordinates (0 : Root) ∧
    slotWeight i 1 - slotWeight i 7 = coordinates (0 : Root) := by decide +kernel

theorem rootA_weight : coordinates (0 : Root) = ![2,2,0,0] := rfl

theorem rootA_long : IsLong (0 : Root) := by decide

end Atlas.F4.Weights
