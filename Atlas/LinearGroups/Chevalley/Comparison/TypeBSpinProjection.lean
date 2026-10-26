import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion
import Atlas.LinearGroups.Chevalley.Comparison.TypeBSpinGamma
import Atlas.LinearGroups.Chevalley.Comparison.TypeBSpinShortOperators

/-! Projection of the primary selected B companion to its literal spin block,
with the same Boolean coordinate marking used by the injective gamma map. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeB
open Classical ClassicalData Integral.Minuscule Atlas.BooleanSpin

def spinMatrixHom (n : ℕ) (hn : 2 ≤ n+1) (R : Type*) [CommRing R] :
    SelectedWeightCompanion (.B (n+1) hn) R →*
      Matrix (SpinIndex n) (SpinIndex n) R where
  toFun g := spinReindex n R (g.val.2 ()).val
  map_one' := map_one (spinReindex n R)
  map_mul' g h := map_mul (spinReindex n R) (g.val.2 ()).val (h.val.2 ()).val

def spinMatrixGamma (n : ℕ) (R : Type*) [CommRing R] :
    Atlas.Orthogonal.VectorB (n+1) R →ₗ[R] Matrix (SpinIndex n) (SpinIndex n) R :=
  (matrix R).toLinearMap.comp (spinGamma (n+1) R)

theorem spinMatrixGamma_injective (n : ℕ) (R : Type*) [CommRing R] :
    Function.Injective (spinMatrixGamma n R) :=
  (matrix R).injective.comp (spinGamma_injective (n+1) R)

theorem spinMatrixHom_X (n : ℕ) (hn : 2 ≤ n+1) (R : Type*) [CommRing R]
    (i : Fin (n+1)) (t : R) :
    spinMatrixHom n hn R (selectedWeightCompanionX (.B (n+1) hn) R i t) =
      spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
        (simpleB n i) (-1) t) := rfl

theorem spinMatrixHom_Y (n : ℕ) (hn : 2 ≤ n+1) (R : Type*) [CommRing R]
    (i : Fin (n+1)) (t : R) :
    spinMatrixHom n hn R (selectedWeightCompanionY (.B (n+1) hn) R i t) =
      spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
        (simpleB n i) 1 t) := rfl

theorem spinMatrixHom_inv_X (n : ℕ) (hn : 2 ≤ n+1) (R : Type*) [CommRing R]
    (i : Fin (n+1)) (t : R) :
    spinMatrixHom n hn R ((selectedWeightCompanionX (.B (n+1) hn) R i t)⁻¹) =
      spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
        (simpleB n i) (-1) (-t)) := rfl

theorem spinMatrixHom_inv_Y (n : ℕ) (hn : 2 ≤ n+1) (R : Type*) [CommRing R]
    (i : Fin (n+1)) (t : R) :
    spinMatrixHom n hn R ((selectedWeightCompanionY (.B (n+1) hn) R i t)⁻¹) =
      spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
        (simpleB n i) 1 (-t)) := rfl

end Atlas.Chevalley.Comparison.TypeB
