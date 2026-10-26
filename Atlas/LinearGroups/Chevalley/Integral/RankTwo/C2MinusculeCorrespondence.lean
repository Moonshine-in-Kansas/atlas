import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2MinusculeIndex
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2MinusculeTemplate
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! The four-coordinate map is the actual selected weight
block. It is jointly faithful with the actual adjoint block; no assertion of
faithfulness of either component, or of the full projection kernel, is made. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo.C2Minuscule
open Classical ClassicalData Integral.Minuscule
open scoped Matrix
set_option maxRecDepth 8192

abbrev C2 := RootType.C 2 (by decide)
abbrev Companion (R : Type*) [CommRing R] := SelectedWeightCompanion C2 R
local instance c2CompanionCorrespondenceRankNeZero : NeZero C2.rank := ⟨by decide⟩

variable (R : Type*) [CommRing R]

def reindex : Matrix (WeightOrbit (pairingC 2) (TypeC.orbit 2))
    (WeightOrbit (pairingC 2) (TypeC.orbit 2)) R ≃ₐ[R] Matrix (Fin 4) (Fin 4) R :=
  Matrix.reindexAlgEquiv R R indexEquiv.symm

/-- Literal restriction to the unique selected weight summand. -/
def weightMatrixHom : Companion R →* Matrix (Fin 4) (Fin 4) R where
  toFun g := reindex R (g.val.2 ()).val
  map_one' := map_one (reindex R)
  map_mul' g h := map_mul (reindex R) (g.val.2 ()).val (h.val.2 ()).val

/-- The two existing blocks together determine an actual companion element. -/
theorem ext (g h : Companion R)
    (hadj : selectedWeightCompanionRho C2 R g = selectedWeightCompanionRho C2 R h)
    (hweight : weightMatrixHom R g = weightMatrixHom R h) : g = h := by
  apply Subtype.ext
  apply Prod.ext
  · exact hadj
  · funext a
    cases a
    apply Units.ext
    exact (reindex R).injective hweight

theorem raising_step (k : Fin 2) :
    reindex R ((TypeC.actualStrings 2).stepMatrix R (baseCIndexEquiv 1 k).val (-1)) =
      (![ea, eb] k).map (Int.castRingHom R) := by
  ext i j
  change (TypeC.actualStrings 2).stepMatrix R (baseCIndexEquiv 1 k).val (-1)
      (weightLabel i) (weightLabel j) = _
  rw [actual_step_entry]
  have htable :
      (if grades k j = -1 ∧ reflected k j = i then (1 : ℤ) else 0) =
        (![ea, eb] k) i j := by
    fin_cases k <;> fin_cases i <;> fin_cases j <;> decide
  rw [Matrix.map_apply, ← htable]
  split_ifs <;> simp only [map_one, map_zero]

theorem lowering_step (k : Fin 2) :
    reindex R ((TypeC.actualStrings 2).stepMatrix R (baseCIndexEquiv 1 k).val 1) =
      (![fa, fb] k).map (Int.castRingHom R) := by
  ext i j
  change (TypeC.actualStrings 2).stepMatrix R (baseCIndexEquiv 1 k).val 1
      (weightLabel i) (weightLabel j) = _
  rw [actual_step_entry]
  have htable :
      (if grades k j = 1 ∧ reflected k j = i then (1 : ℤ) else 0) =
        (![fa, fb] k) i j := by
    fin_cases k <;> fin_cases i <;> fin_cases j <;> decide
  rw [Matrix.map_apply, ← htable]
  split_ifs <;> simp only [map_one, map_zero]

variable {R}

theorem matrix_X (k : Fin 2) (t : R) :
    weightMatrixHom R (selectedWeightCompanionX C2 R k t) =
      1 + t • (![ea, eb] k).map (Int.castRingHom R) := by
  change reindex R ((TypeC.actualStrings 2).rootMatrix R
      (baseCIndexEquiv 1 k).val (-1) t) = _
  rw [Minuscule.Strings.rootMatrix, map_add, map_one, map_smul, raising_step]

theorem matrix_Y (k : Fin 2) (t : R) :
    weightMatrixHom R (selectedWeightCompanionY C2 R k t) =
      1 + t • (![fa, fb] k).map (Int.castRingHom R) := by
  change reindex R ((TypeC.actualStrings 2).rootMatrix R
      (baseCIndexEquiv 1 k).val 1 t) = _
  rw [Minuscule.Strings.rootMatrix, map_add, map_one, map_smul, lowering_step]

theorem matrix_xshort (t : R) :
    weightMatrixHom R (selectedWeightCompanionX C2 R 0 t) = XA t := matrix_X 0 t
theorem matrix_xlong (t : R) :
    weightMatrixHom R (selectedWeightCompanionX C2 R 1 t) = XB t := matrix_X 1 t
theorem matrix_yshort (t : R) :
    weightMatrixHom R (selectedWeightCompanionY C2 R 0 t) = YA t := matrix_Y 0 t
theorem matrix_ylong (t : R) :
    weightMatrixHom R (selectedWeightCompanionY C2 R 1 t) = YB t := matrix_Y 1 t

end Atlas.Chevalley.Integral.RankTwo.C2Minuscule
