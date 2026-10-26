import Atlas.LinearGroups.Chevalley.G2PositivePairCommutators
import Atlas.LinearGroups.Chevalley.WeightCompanionTorus
import Atlas.LinearGroups.Chevalley.Integral.MinusculeTripleEdgeTrivial

/-! Source candidates: the remaining fourteen G2 pair relations in the actual
full companion. Literal block equality replaces any projection-injectivity premise. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Integral Integral.Minuscule
open scoped commutatorElement
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]
include hdiamond

/-- The literal pair relations in the simultaneous adjoint/minuscule subgroup. -/
theorem weightCompanion_g2_positive_pairs_twoStep_and_commute
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3)
    (s t : R) :
    let ni := weightCompanionWeyl P b O hc hm R i 1
    let nj := weightCompanionWeyl P b O hc hm R j 1
    let Z (u : R) := nj * weightCompanionX P b O hc hm R i u * nj⁻¹
    let W (u : R) := (ni * nj) * weightCompanionX P b O hc hm R i u * (ni * nj)⁻¹
    let V (u : R) := ni * weightCompanionX P b O hc hm R j u * ni⁻¹
    let H (u : R) := (nj * ni) * weightCompanionX P b O hc hm R j u * (nj * ni)⁻¹
    ⁅weightCompanionX P b O hc hm R i s, W t⁆ = V (3*s*t) ∧
    ⁅weightCompanionX P b O hc hm R j s, V t⁆ = H (s*t) ∧
    ⁅Z s, W t⁆ = H (3*s*t) ∧
    Commute (weightCompanionX P b O hc hm R i s) (V t) ∧
    Commute (weightCompanionX P b O hc hm R i s) (H t) ∧
    Commute (weightCompanionX P b O hc hm R j s) (Z t) ∧
    Commute (weightCompanionX P b O hc hm R j s) (W t) ∧
    Commute (weightCompanionX P b O hc hm R j s) (H t) ∧
    Commute (Z s) (V t) ∧ Commute (Z s) (H t) ∧
    Commute (W s) (V t) ∧ Commute (W s) (H t) ∧ Commute (V s) (H t) := by
  classical
  let π (a : κ) : WeightCompanion P b O hc hm R →*
      (Matrix (WeightOrbit P (O a)) (WeightOrbit P (O a)) R)ˣ :=
    { toFun := fun (g : WeightCompanion P b O hc hm R) => g.val.2 a
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hxi (a : κ) (u : R) : π a (weightCompanionX P b O hc hm R i u) = 1 :=
    weightOrbit_tripleEdge_rootElement_eq_one P (O a) (hc a) (hm a) R
      i.val j.val i.val hij hji (Or.inl rfl) (-1) (by decide) u
  have hxj (a : κ) (u : R) : π a (weightCompanionX P b O hc hm R j u) = 1 :=
    weightOrbit_tripleEdge_rootElement_eq_one P (O a) (hc a) (hm a) R
      i.val j.val j.val hij hji (Or.inr rfl) (-1) (by decide) u
  have hni (a : κ) : π a (weightCompanionWeyl P b O hc hm R i 1) = 1 :=
    weightOrbit_tripleEdge_weylMatrixUnit_eq_one P (O a) (hc a) (hm a) R
      i.val j.val i.val hij hji (Or.inl rfl) 1
  have hnj (a : κ) : π a (weightCompanionWeyl P b O hc hm R j 1) = 1 :=
    weightOrbit_tripleEdge_weylMatrixUnit_eq_one P (O a) (hc a) (hm a) R
      i.val j.val j.val hij hji (Or.inr rfl) 1
  have lift (g h : WeightCompanion P b O hc hm R)
      (hadj : g.val.1 = h.val.1) (hmini : ∀ a, π a g = π a h) : g = h := by
    apply Subtype.ext
    exact Prod.ext hadj (funext hmini)
  have h := adjoint_g2_positive_pairs_twoStep_and_commute P b hdiamond R i j hne hij hji s t
  dsimp only at h ⊢
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13⟩ := h
  refine ⟨lift _ _ h1 ?_,lift _ _ h2 ?_,lift _ _ h3 ?_,lift _ _ h4.eq ?_,lift _ _ h5.eq ?_,lift _ _ h6.eq ?_,lift _ _ h7.eq ?_,lift _ _ h8.eq ?_,lift _ _ h9.eq ?_,lift _ _ h10.eq ?_,lift _ _ h11.eq ?_,lift _ _ h12.eq ?_,lift _ _ h13.eq ?_⟩
  all_goals
    intro a
    simp only [map_commutatorElement, map_mul, map_inv, hxi, hxj, hni, hnj,
      commutatorElement_def, inv_one, one_mul]

/-- The literal pair relations in the simultaneous adjoint/minuscule subgroup. -/
theorem weightCompanionX_g2_short_pair_commutator
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3)
    (s t : R) :
    let ni := weightCompanionWeyl P b O hc hm R i 1
    let nj := weightCompanionWeyl P b O hc hm R j 1
    ⁅weightCompanionX P b O hc hm R i s, nj * weightCompanionX P b O hc hm R i t * nj⁻¹⁆ =
      ((ni*nj) * weightCompanionX P b O hc hm R i (-2*s*t) * (ni*nj)⁻¹) *
      (ni * weightCompanionX P b O hc hm R j (-3*s^2*t) * ni⁻¹) *
      ((nj*ni) * weightCompanionX P b O hc hm R j (-3*s*t^2) * (nj*ni)⁻¹) := by
  classical
  let π (a : κ) : WeightCompanion P b O hc hm R →*
      (Matrix (WeightOrbit P (O a)) (WeightOrbit P (O a)) R)ˣ :=
    { toFun := fun (g : WeightCompanion P b O hc hm R) => g.val.2 a
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hxi (a : κ) (u : R) : π a (weightCompanionX P b O hc hm R i u) = 1 :=
    weightOrbit_tripleEdge_rootElement_eq_one P (O a) (hc a) (hm a) R
      i.val j.val i.val hij hji (Or.inl rfl) (-1) (by decide) u
  have hxj (a : κ) (u : R) : π a (weightCompanionX P b O hc hm R j u) = 1 :=
    weightOrbit_tripleEdge_rootElement_eq_one P (O a) (hc a) (hm a) R
      i.val j.val j.val hij hji (Or.inr rfl) (-1) (by decide) u
  have hni (a : κ) : π a (weightCompanionWeyl P b O hc hm R i 1) = 1 :=
    weightOrbit_tripleEdge_weylMatrixUnit_eq_one P (O a) (hc a) (hm a) R
      i.val j.val i.val hij hji (Or.inl rfl) 1
  have hnj (a : κ) : π a (weightCompanionWeyl P b O hc hm R j 1) = 1 :=
    weightOrbit_tripleEdge_weylMatrixUnit_eq_one P (O a) (hc a) (hm a) R
      i.val j.val j.val hij hji (Or.inr rfl) 1
  have lift (g h : WeightCompanion P b O hc hm R)
      (hadj : g.val.1 = h.val.1) (hmini : ∀ a, π a g = π a h) : g = h := by
    apply Subtype.ext
    exact Prod.ext hadj (funext hmini)
  have h := adjointX_g2_short_pair_commutator P b hdiamond R i j hne hij hji s t
  dsimp only at h ⊢
  apply lift _ _ h
  intro a
  simp only [map_commutatorElement, map_mul, map_inv, hxi, hxj, hni, hnj,
    commutatorElement_def, inv_one, one_mul]

end Atlas.Chevalley
