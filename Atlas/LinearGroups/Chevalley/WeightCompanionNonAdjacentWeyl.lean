import Atlas.LinearGroups.Chevalley.Integral.MinusculeNonAdjacent
import Atlas.LinearGroups.Chevalley.Integral.NonAdjacentCommutation
import Atlas.LinearGroups.Chevalley.WeightCompanionCommutation
import Atlas.LinearGroups.Chevalley.WeightCompanionTorus

/-! Source candidate: actual nonadjacent Weyl words commute on the complete
simultaneous companion, not merely on its adjoint projection. -/

noncomputable section
namespace Atlas.Chevalley

private theorem commute_three_factor_words {G : Type*} [Semigroup G]
    (x y z w : G) (hxz : Commute x z) (hxw : Commute x w)
    (hyz : Commute y z) (hyw : Commute y w) :
    Commute (x * y * x) (z * w * z) := by
  have hx : Commute x (z * w * z) := (hxz.mul_right hxw).mul_right hxz
  have hy : Commute y (z * w * z) := (hyz.mul_right hyw).mul_right hyz
  exact (hx.mul_left hy).mul_left hx

universe u
open Classical Integral Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

include hdiamond

theorem weightCompanionX_commute_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0) (s t : R) :
    Commute (weightCompanionX P b O hc hm R i s)
      (weightCompanionX P b O hc hm R j t) := by
  have hij : b.cartanMatrix i j = 0 := b.cartanMatrix_apply_eq_zero_iff_symm.mpr hji
  change _ * _ = _ * _
  apply Subtype.ext
  apply Prod.ext
  · exact (adjointX_commute_of_zero_cartan P b hdiamond R i j hne hji s t).eq
  · funext a
    exact (weightOrbit_rootElements_commute_of_zero P (O a) (hc a) (hm a)
      i.val j.val hij hji R (-1) (-1) (by decide) (by decide) s t).eq

theorem weightCompanionY_commute_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0) (s t : R) :
    Commute (weightCompanionY P b O hc hm R i s)
      (weightCompanionY P b O hc hm R j t) := by
  have hij : b.cartanMatrix i j = 0 := b.cartanMatrix_apply_eq_zero_iff_symm.mpr hji
  change _ * _ = _ * _
  apply Subtype.ext
  apply Prod.ext
  · exact (adjointY_commute_of_zero_cartan P b hdiamond R i j hne hji s t).eq
  · funext a
    exact (weightOrbit_rootElements_commute_of_zero P (O a) (hc a) (hm a)
      i.val j.val hij hji R 1 1 (by decide) (by decide) s t).eq

/-- The length-two braid relation holds for the literal Weyl words, with
arbitrary unit parameters, over all commutative coefficient rings. -/
theorem weightCompanionWeyl_commute_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0) (a c : Rˣ) :
    Commute (weightCompanionWeyl P b O hc hm R i a)
      (weightCompanionWeyl P b O hc hm R j c) := by
  unfold weightCompanionWeyl
  exact commute_three_factor_words _ _ _ _
    (weightCompanionX_commute_of_zero_cartan P b hdiamond O hc hm R i j hne hji a.val c.val)
    (weightCompanionX_commute_Y P b hdiamond O hc hm R i j hne a.val (-c.inv))
    (weightCompanionX_commute_Y P b hdiamond O hc hm R j i hne.symm c.val (-a.inv)).symm
    (weightCompanionY_commute_of_zero_cartan P b hdiamond O hc hm R i j hne hji (-a.inv) (-c.inv))

end Atlas.Chevalley
