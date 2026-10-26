import Atlas.LinearGroups.Chevalley.Integral.NonAdjacentCommutation
import Atlas.LinearGroups.Chevalley.ModelOppositeSimple

/-! Source candidate: the actual all-type dispatcher discharges the
local-diamond prerequisite for nonadjacent simple-root commutation. -/

noncomputable section
namespace Atlas.Chevalley

/-- Nonadjacent positive simple-root groups in each new model commute. -/
theorem modelX_commute_of_zero_cartan
    (Φ : RootType) (R : Type*) [CommRing R]
    (i j : Fin Φ.rank) (hne : i ≠ j)
    (hji : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = 0) (s t : R) :
    Commute (modelX Φ R i s) (modelX Φ R j t) :=
  adjointX_commute_of_zero_cartan (rootDatum Φ).pairing (rootDatum Φ).base
    (rootDatum_simpleDiamondProducts Φ) R _ _
    (fun h => hne ((rootDatum Φ).indexEquiv.injective h)) hji s t

/-- Nonadjacent negative simple-root groups in each new model commute. -/
theorem modelY_commute_of_zero_cartan
    (Φ : RootType) (R : Type*) [CommRing R]
    (i j : Fin Φ.rank) (hne : i ≠ j)
    (hji : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = 0) (s t : R) :
    Commute (modelY Φ R i s) (modelY Φ R j t) :=
  adjointY_commute_of_zero_cartan (rootDatum Φ).pairing (rootDatum Φ).base
    (rootDatum_simpleDiamondProducts Φ) R _ _
    (fun h => hne ((rootDatum Φ).indexEquiv.injective h)) hji s t

end Atlas.Chevalley
