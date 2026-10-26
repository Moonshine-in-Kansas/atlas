import Atlas.LinearGroups.Chevalley.Comparison.TypeAWeightBlock
import Atlas.LinearGroups.Chevalley.WeightCompanionLeftInduction
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! The literal defining weight block has determinant one, giving the
marked comparison homomorphism from the new companion to SL. Surjectivity,
injectivity and the projective comparison remain separate obligations. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeA
open Classical

theorem adjacent_ne {r : ℕ} (i : Fin r) : i.castSucc ≠ i.succ := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ] at hv
  omega

theorem weightMatrix_det (r : ℕ) (hr : 1 ≤ r) (R : Type*) [CommRing R]
    (g : SelectedWeightCompanion (.A r hr) R) :
    Matrix.det (weightMatrixHom r hr R g) = 1 := by
  apply weightCompanion_induction_left (rootDatum (.A r hr)).pairing
    (rootDatum (.A r hr)).base (selectedWeightOrbits (.A r hr))
    (selectedWeightOrbits_closed (.A r hr))
    (selectedWeightOrbits_minuscule (.A r hr)) R ?_ ?_ ?_ g
  · simp only [map_one, Matrix.det_one]
  · intro j t h hh
    obtain ⟨i, rfl⟩ := (rootDatum (.A r hr)).indexEquiv.surjective j
    change Fin r at i
    change Matrix.det (weightMatrixHom r hr R
      (selectedWeightCompanionX (.A r hr) R i t * h)) = 1
    rw [map_mul, Matrix.det_mul, matrix_X r hr R i t,
      Matrix.det_transvection_of_ne _ _ (adjacent_ne i), hh, one_mul]
  · intro j t h hh
    obtain ⟨i, rfl⟩ := (rootDatum (.A r hr)).indexEquiv.surjective j
    change Fin r at i
    change Matrix.det (weightMatrixHom r hr R
      (selectedWeightCompanionY (.A r hr) R i t * h)) = 1
    rw [map_mul, Matrix.det_mul, matrix_Y r hr R i t,
      Matrix.det_transvection_of_ne _ _ (adjacent_ne i).symm, hh, one_mul]

def specialLinearHom (r : ℕ) (hr : 1 ≤ r) (R : Type*) [CommRing R] :
    SelectedWeightCompanion (.A r hr) R →*
      Matrix.SpecialLinearGroup (Fin (r + 1)) R where
  toFun g := ⟨weightMatrixHom r hr R g, weightMatrix_det r hr R g⟩
  map_one' := Subtype.ext (map_one (weightMatrixHom r hr R))
  map_mul' g h := Subtype.ext (map_mul (weightMatrixHom r hr R) g h)

theorem specialLinearHom_X (r : ℕ) (hr : 1 ≤ r) (R : Type*) [CommRing R]
    (i : Fin r) (t : R) :
    specialLinearHom r hr R (selectedWeightCompanionX (.A r hr) R i t) =
      Matrix.SpecialLinearGroup.transvection (adjacent_ne i) t :=
  Subtype.ext (matrix_X r hr R i t)

theorem specialLinearHom_Y (r : ℕ) (hr : 1 ≤ r) (R : Type*) [CommRing R]
    (i : Fin r) (t : R) :
    specialLinearHom r hr R (selectedWeightCompanionY (.A r hr) R i t) =
      Matrix.SpecialLinearGroup.transvection (adjacent_ne i).symm t :=
  Subtype.ext (matrix_Y r hr R i t)

end Atlas.Chevalley.Comparison.TypeA
