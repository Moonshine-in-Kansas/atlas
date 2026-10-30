import Atlas.LinearGroups.Chevalley.Comparison.F4.GeckOperators
import Atlas.LinearGroups.Chevalley.Comparison.F4.Conjugation
import Atlas.LinearGroups.Chevalley.Models

/-! Identification with the actual Geck exponentials. Integral divided powers
are evaluated before base change; coefficient rings never divide by 2 or 3.
-/
noncomputable section
namespace Atlas.Chevalley.Comparison.F4
open Integral F4Data
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

private theorem square_identity (i : Fin 8) :
    geckMatrix i * geckMatrix i = 2 • geckSecondMatrix i := by
  fin_cases i
  all_goals first
    | exact geck_square_0 | exact geck_square_1 | exact geck_square_2
    | exact geck_square_3 | exact geck_square_4 | exact geck_square_5
    | exact geck_square_6 | exact geck_square_7

private theorem cube_identity (i : Fin 8) :
    geckSecondMatrix i * geckMatrix i = 0 := by
  fin_cases i
  all_goals first
    | exact geck_cube_0 | exact geck_cube_1 | exact geck_cube_2
    | exact geck_cube_3 | exact geck_cube_4 | exact geck_cube_5
    | exact geck_cube_6 | exact geck_cube_7

private theorem geck_pow_three (i : Fin 8) : geckMatrix i ^ 3 = 0 := by
  calc
    _ = (geckMatrix i * geckMatrix i) * geckMatrix i := by simp [pow_succ, pow_two]
    _ = (2 • geckSecondMatrix i) * geckMatrix i := by rw [square_identity]
    _ = 2 • (geckSecondMatrix i * geckMatrix i) := smul_mul_assoc _ _ _
    _ = 0 := by rw [cube_identity, smul_zero]

theorem geck_divided_coefficients (i : Fin 8) (n : Fin 4) (a c : Fin 52) :
    ((geckMatrix i ^ n.val) a c / (n.val.factorial : ℤ)) =
      (![1,geckMatrix i,geckSecondMatrix i,0] n) a c := by
  fin_cases n
  · change (1 : Matrix (Fin 52) (Fin 52) ℤ) a c / 1 =
      (1 : Matrix (Fin 52) (Fin 52) ℤ) a c
    exact Int.ediv_one _
  · change (geckMatrix i ^ 1) a c / 1 = geckMatrix i a c
    rw [pow_one, Int.ediv_one]
  · have h := congrArg (fun M : Matrix (Fin 52) (Fin 52) ℤ => M a c) (square_identity i)
    simp only [two_smul, Matrix.add_apply] at h
    change (geckMatrix i ^ 2) a c / 2 = geckSecondMatrix i a c
    rw [pow_two, h]
    omega
  · change (geckMatrix i ^ 3) a c / 6 = 0
    rw [geck_pow_three]
    rfl

private theorem reindex52_divided_entry (i : Fin 4) (n : ℕ) (a c : Fin 52) :
    raisingDividedPower pairing base (baseIndexEquiv i) n
      (coordinateEquiv52 a) (coordinateEquiv52 c) =
      (geckMatrix (Fin.castAdd 4 i) ^ n) a c / (n.factorial : ℤ) := by
  have h := congrArg (fun M : Matrix (Fin 52) (Fin 52) ℤ => M a c)
    ((reindex52 ℤ).map_pow (raising pairing base (baseIndexEquiv i)) n)
  rw [reindex52_raising] at h
  change (raising pairing base (baseIndexEquiv i) ^ n)
    (coordinateEquiv52 a) (coordinateEquiv52 c) = _ at h
  unfold raisingDividedPower
  exact congrArg (fun z : ℤ => z/(n.factorial : ℤ)) h

variable {R : Type*} [CommRing R]

theorem actual_raising_exponential (i : Fin 4) (t : R) :
    reindex52 R (raisingExponential pairing base R (baseIndexEquiv i) t) =
      geckOver R (Fin.castAdd 4 i) t := by
  ext a c
  change raisingExponential pairing base R (baseIndexEquiv i) t
    (coordinateEquiv52 a) (coordinateEquiv52 c) = _
  simp only [raisingExponential_expansion, raisingDividedOver, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, reindex52_divided_entry]
  erw [geck_divided_coefficients _ (0 : Fin 4),
    geck_divided_coefficients _ (1 : Fin 4),
    geck_divided_coefficients _ (2 : Fin 4),
    geck_divided_coefficients _ (3 : Fin 4)]
  change (algebraMap ℤ R) ((1 : Matrix (Fin 52) (Fin 52) ℤ) a c) +
    t * (algebraMap ℤ R) (geckMatrix (Fin.castAdd 4 i) a c) +
    t^2 * (algebraMap ℤ R) (geckSecondMatrix (Fin.castAdd 4 i) a c) +
    t^3 * (algebraMap ℤ R) 0 = _
  simp only [geckOver, Matrix.map_apply, Matrix.one_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, apply_ite, map_one, map_zero, mul_zero, add_zero,
    algebraMap_int_eq]

/-- A faithful reindexing of the specified Chevalley model, not a new model. -/
def chevalleyMatrixHom : Atlas.Chevalley.Model .F4 R →* Matrix (Fin 52) (Fin 52) R where
  toFun g := reindex52 R g.val.val
  map_one' := map_one (reindex52 R)
  map_mul' g h := map_mul (reindex52 R) g.val.val h.val.val

theorem chevalleyMatrixHom_injective : Function.Injective (chevalleyMatrixHom (R:=R)) := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  exact (reindex52 R).injective he

theorem chevalleyMatrixHom_X (i : Fin 4) (t : R) :
    chevalleyMatrixHom (modelX .F4 R i t) = geckOver R (Fin.castAdd 4 i) t :=
  actual_raising_exponential i t

end Atlas.Chevalley.Comparison.F4
