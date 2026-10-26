import Atlas.LinearGroups.ReeF4.StarRootTargets
import Atlas.LinearGroups.ReeF4.RootVectors
import Atlas.Algebra.Albert.TraceZeroScalarForms

/-! An additive realization of the corrected coset-dependent opposite-pair rule.
This verifies the opposite-pair relations, not the complete star map. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def oppositeLabelValue (r : ShortRootLabel) : TraceZero F :=
  if r.2 = 0 ∨ r.2 = 7 then 0
  else if r.2 = 1 ∨ r.2 = 6 then diagonalVector 0
  else if r.2 = 2 ∨ r.2 = 5 then diagonalVector 2
  else diagonalVector 1

theorem oppositeLabelValue_map {R : Type*} [CommRing R] [CharP R 2]
    (f : F →+* R) (r : ShortRootLabel) :
    traceZeroMap f (oppositeLabelValue r) = oppositeLabelValue r := by
  unfold oppositeLabelValue
  split_ifs <;> simp [diagonalVector_map, traceZeroMap_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- The finite integer root table identifies the coset for each perpendicular pair.
private theorem oppositeLabelValue_pair_binary : ∀ r s : ShortRootLabel,
    rootDot (scaledShortRoot r) (scaledShortRoot s) = 0 →
    oppositeLabelValue (F := ZMod 2) r + oppositeLabelValue s =
      diagonalVector (starRootTarget r s).1 := by
  intro r s
  fin_cases r <;> fin_cases s <;> decide

theorem oppositeLabelValue_pair (r s : ShortRootLabel)
    (hp : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0) :
    oppositeLabelValue (F := F) r + oppositeLabelValue s =
      diagonalVector (starRootTarget r s).1 := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have hm (u v : TraceZero (ZMod 2)) : traceZeroMap f (u + v) =
      traceZeroMap f u + traceZeroMap f v := by
    apply Subtype.ext
    exact Atlas.Albert.map_add f u.val v.val
  have h := congrArg (traceZeroMap f) (oppositeLabelValue_pair_binary r s hp)
  simpa only [hm, oppositeLabelValue_map, diagonalVector_map] using h

theorem oppositeLabelValue_cycle (r s t : ShortRootLabel) :
    (oppositeLabelValue (F := F) r + oppositeLabelValue s) +
      (oppositeLabelValue s + oppositeLabelValue t) =
        oppositeLabelValue r + oppositeLabelValue t := by
  have h : oppositeLabelValue (F := F) s + oppositeLabelValue s = 0 :=
    by rw [← two_smul F, CharTwo.two_eq_zero, zero_smul]
  calc
    _ = oppositeLabelValue r + (oppositeLabelValue s + oppositeLabelValue s) +
        oppositeLabelValue t := by abel
    _ = _ := by rw [h]; simp

end Atlas.ReeF4
