import Atlas.LinearGroups.Chevalley.Integral.A2IntegralSerre
import Atlas.LinearGroups.Chevalley.ModelOppositeSimple

/-! UNCHECKED source-only split of the all-model wrapper. Generic integral
A2 operator relations are kept in the separate preceding module. -/
noncomputable section
namespace Atlas.Chevalley
open Integral

/-- Actual pinned all-type application: the diamond condition is discharged
by its compiled coordinate providers, not supplied as a matrix relation. -/
theorem modelRaising_a2_commute_bracket (Φ : RootType) (R : Type*) [CommRing R]
    (i j : Fin Φ.rank) (hij : i ≠ j)
    (hijc : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) = -1)
    (hjic : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = -1) :
    let E := fun k => raisingOver (rootDatum Φ).pairing (rootDatum Φ).base R
      ((rootDatum Φ).indexEquiv k)
    Commute (E i) (E i * E j - E j * E i) ∧
      Commute (E j) (E i * E j - E j * E i) :=
  raisingOver_a2_commute_bracket (rootDatum Φ).pairing (rootDatum Φ).base
    (rootDatum_simpleDiamondProducts Φ) R _ _
    (fun h => hij ((rootDatum Φ).indexEquiv.injective h)) hijc hjic

end Atlas.Chevalley
