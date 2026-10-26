import Atlas.LinearGroups.Chevalley.B2WeylCommutator
import Atlas.LinearGroups.Chevalley.ModelOppositeSimple

/-! UNCOMPILED source candidate. The double-edge commutator for the actual
dispatched Chevalley models, with the diamond premise discharged. -/

noncomputable section
namespace Atlas.Chevalley
open scoped commutatorElement

/-- The actual double-edge model generators satisfy the pinned integral
commutator word over every commutative ring, including characteristics 2 and 3. -/
theorem modelX_b2_commutator_eq_weyl_product
    (Φ : RootType) (R : Type*) [CommRing R]
    (i j : Fin Φ.rank) (hne : i ≠ j)
    (hij : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) = -1)
    (hji : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = -2)
    (s t : R) :
    let wi := modelX Φ R i 1 * modelY Φ R i (-1) * modelX Φ R i 1
    let wj := modelX Φ R j 1 * modelY Φ R j (-1) * modelX Φ R j 1
    ⁅modelX Φ R i s, modelX Φ R j t⁆ =
      (wj * modelX Φ R i (-s*t) * wj⁻¹) * (wi * modelX Φ R j (s^2*t) * wi⁻¹) :=
  adjointX_b2_commutator_eq_weyl_product (rootDatum Φ).pairing
    (rootDatum Φ).base (rootDatum_simpleDiamondProducts Φ) R _ _
    (fun h => hne ((rootDatum Φ).indexEquiv.injective h)) hij hji s t

end Atlas.Chevalley
