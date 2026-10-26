import Atlas.LinearGroups.Chevalley.A2WeylCommutator
import Atlas.LinearGroups.Chevalley.ModelOppositeSimple

/-! The pinned single-edge commutator in each actual dispatched Chevalley model. -/

noncomputable section
namespace Atlas.Chevalley
open scoped commutatorElement

/-- The diamond premise is discharged from the actual coordinate root datum.
The Weyl representative is the displayed word in the existing model generators. -/
theorem modelX_a2_commutator_eq_weyl_conjugate
    (Φ : RootType) (R : Type*) [CommRing R]
    (i j : Fin Φ.rank) (hne : i ≠ j)
    (hij : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) = -1)
    (hji : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = -1)
    (s t : R) :
    let w := modelX Φ R i 1 * modelY Φ R i (-1) * modelX Φ R i 1
    ⁅modelX Φ R i s, modelX Φ R j t⁆ = w * modelX Φ R j (s*t) * w⁻¹ :=
  adjointX_a2_commutator_eq_weyl_conjugate (rootDatum Φ).pairing
    (rootDatum Φ).base (rootDatum_simpleDiamondProducts Φ) R _ _
    (fun h => hne ((rootDatum Φ).indexEquiv.injective h)) hij hji s t

end Atlas.Chevalley
