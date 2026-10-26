import Atlas.LinearGroups.Chevalley.Models
import Atlas.LinearGroups.Chevalley.Integral.SimplyLacedActualDiamonds
import Atlas.LinearGroups.Chevalley.Integral.BoundedActualDiamonds
import Atlas.LinearGroups.Chevalley.Integral.G2LocalDiamond

/-! Opposite distinct simple roots in the actual all-type dispatcher.
Each arithmetic provider is proved from its coordinate root datum. -/
noncomputable section
namespace Atlas.Chevalley

theorem rootDatum_simpleDiamondProducts (Φ : RootType) :
    Integral.SimpleDiamondProducts (rootDatum Φ).pairing (rootDatum Φ).base := by
  cases Φ with
  | A r hr => exact TypeAData.simpleDiamondProducts r
  | B r hr => exact ClassicalData.simpleDiamondProductsB (r-1)
  | C r hr => exact ClassicalData.simpleDiamondProductsC (r-1)
  | D r hr => exact ClassicalData.simpleDiamondProductsD (r-2)
  | E6 => exact E6Data.simpleDiamondProducts
  | E7 => exact E7Data.simpleDiamondProducts
  | E8 => exact E8Data.simpleDiamondProducts
  | F4 => exact F4Data.simpleDiamondProducts
  | G2 => exact G2Data.simpleDiamondProducts

/-- Uniform actual-model relation, including all coefficient characteristics. -/
theorem modelX_commute_modelY (Φ : RootType) (R : Type*) [CommRing R]
    (i j : Fin Φ.rank) (hij : i ≠ j) (s t : R) :
    Commute (modelX Φ R i s) (modelY Φ R j t) :=
  adjointX_commute_adjointY_of_diamond (rootDatum Φ).pairing (rootDatum Φ).base
    (rootDatum_simpleDiamondProducts Φ) R _ _
    (fun h => hij ((rootDatum Φ).indexEquiv.injective h)) s t

theorem modelY_commute_modelX (Φ : RootType) (R : Type*) [CommRing R]
    (i j : Fin Φ.rank) (hij : i ≠ j) (s t : R) :
    Commute (modelY Φ R i s) (modelX Φ R j t) :=
  (modelX_commute_modelY Φ R j i hij.symm t s).symm

end Atlas.Chevalley
