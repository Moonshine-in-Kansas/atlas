import Atlas.LinearGroups.Chevalley.Integral.A2CommutatorProduct
import Atlas.LinearGroups.Chevalley.ModelOppositeSimple

/-! The single-edge product law in the actual generated groups. The all-type
wrapper discharges the generic diamond premise with the compiled root data. -/
noncomputable section
namespace Atlas.Chevalley
open Integral
open scoped commutatorElement

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R]

include hdiamond in
theorem adjointX_a2_commutator_depends_on_product
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1)
    (s t : R) :
    ⁅adjointX P b R i s, adjointX P b R j t⁆ =
      ⁅adjointX P b R i 1, adjointX P b R j (s*t)⁆ := by
  apply Subtype.ext
  apply Units.ext
  exact raisingExponential_a2_commutator_depends_on_product
    P b hdiamond R i j hne hij hji s t

/-- This is an equality in Model Φ R, with no diamond or matrix-relation
hypothesis left for its actual root data. -/
theorem modelX_a2_commutator_depends_on_product
    (Φ : RootType) (R : Type*) [CommRing R]
    (i j : Fin Φ.rank) (hne : i ≠ j)
    (hij : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) = -1)
    (hji : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = -1)
    (s t : R) :
    ⁅modelX Φ R i s, modelX Φ R j t⁆ =
      ⁅modelX Φ R i 1, modelX Φ R j (s*t)⁆ :=
  adjointX_a2_commutator_depends_on_product (rootDatum Φ).pairing
    (rootDatum Φ).base (rootDatum_simpleDiamondProducts Φ) R _ _
    (fun h => hne ((rootDatum Φ).indexEquiv.injective h)) hij hji s t

end Atlas.Chevalley
