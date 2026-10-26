import Atlas.LinearGroups.Chevalley.WeightCompanionTorus
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Group

/-! The literal same-root big-cell identity, before any Bruhat decomposition.
The units statement works in every commutative ring. No root-coherence,
diamond, field cardinality, or projection-kernel hypothesis is used. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)

/-- Cancel the two literal positive-root factors in the definition of n(a).
This identity uses only the additive root law and h(a)=n(a)n(1)⁻¹. -/
theorem weightCompanionY_neg_inv_eq_rankOne_product
    (R : Type*) [CommRing R] (i : b.support) (a : Rˣ) :
    weightCompanionY P b O hc hm R i (-(↑(a⁻¹) : R)) =
      weightCompanionX P b O hc hm R i (-(↑a : R)) *
        weightCompanionTorus P b O hc hm R i a *
          weightCompanionWeyl P b O hc hm R i 1 *
            weightCompanionX P b O hc hm R i (-(↑a : R)) := by
  have hxneg : weightCompanionX P b O hc hm R i (-(↑a : R)) =
      (weightCompanionX P b O hc hm R i (↑a : R))⁻¹ :=
    map_inv (weightCompanionXHom P b O hc hm R i) (Multiplicative.ofAdd (↑a : R))
  change weightCompanionY P b O hc hm R i (-(↑(a⁻¹) : R)) =
    weightCompanionX P b O hc hm R i (-(↑a : R)) *
      ((weightCompanionX P b O hc hm R i (↑a : R) *
          weightCompanionY P b O hc hm R i (-(↑(a⁻¹) : R)) *
            weightCompanionX P b O hc hm R i (↑a : R)) *
        (weightCompanionWeyl P b O hc hm R i 1)⁻¹) *
      weightCompanionWeyl P b O hc hm R i 1 *
        weightCompanionX P b O hc hm R i (-(↑a : R))
  rw [hxneg]
  group

/-- The ring-unit version of y(t)=x(t⁻¹)h(-t⁻¹)n(1)x(t⁻¹). -/
theorem weightCompanionY_unit_eq_rankOne_product
    (R : Type*) [CommRing R] (i : b.support) (a : Rˣ) :
    weightCompanionY P b O hc hm R i (↑a : R) =
      weightCompanionX P b O hc hm R i (↑(a⁻¹) : R) *
        weightCompanionTorus P b O hc hm R i (-a⁻¹) *
          weightCompanionWeyl P b O hc hm R i 1 *
            weightCompanionX P b O hc hm R i (↑(a⁻¹) : R) := by
  simpa only [inv_neg, inv_inv, Units.val_neg, neg_neg] using
    weightCompanionY_neg_inv_eq_rankOne_product P b O hc hm R i (-a⁻¹)

/-- Over a field the only excluded parameter is zero. -/
theorem weightCompanionY_eq_rankOne_product_of_ne_zero
    (K : Type*) [Field K] (i : b.support) (t : K) (ht : t ≠ 0) :
    weightCompanionY P b O hc hm K i t =
      weightCompanionX P b O hc hm K i t⁻¹ *
        weightCompanionTorus P b O hc hm K i (-(Units.mk0 t ht)⁻¹) *
          weightCompanionWeyl P b O hc hm K i 1 *
            weightCompanionX P b O hc hm K i t⁻¹ :=
  weightCompanionY_unit_eq_rankOne_product P b O hc hm K i (Units.mk0 t ht)

end Atlas.Chevalley
