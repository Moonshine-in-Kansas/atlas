import Atlas.GroupTheory.CommutatorHomCentralization
import Atlas.LinearGroups.Chevalley.WeightCompanionA2Transport
import Atlas.LinearGroups.Chevalley.WeightCompanionB2ShortShort

/-! Complete literal positive-pair tables for A2 and B2. The two-root
A1×A1 table is already weightCompanionX_commute_of_zero_cartan.
All statements are in the actual full companion over every commutative ring. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
open scoped commutatorElement

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

/-- The three unordered distinct positive pairs in A2, in the literal
pinning Z(t)=n_i X_j(t)n_i⁻¹. -/
theorem weightCompanion_a2_positive_pairs
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1)
    (s t : R) :
    let X := weightCompanionX P b O hc hm R i
    let Y := weightCompanionX P b O hc hm R j
    let ni := weightCompanionWeyl P b O hc hm R i 1
    let Z := fun a => ni * Y a * ni⁻¹
    ⁅X s, Y t⁆ = Z (s * t) ∧ Commute (X s) (Z t) ∧ Commute (Y s) (Z t) := by
  refine ⟨weightCompanionX_a2_commutator_eq_weyl_conjugate
    P b hdiamond O hc hm R i j hne hij hji s t, ?_, ?_⟩
  · exact weightCompanionX_commute_sameWeyl_conjugate_X
      P b O hc hm R hdiamond i j hne s t
  · have h := weightCompanionX_commute_sameWeyl_conjugate_X
      P b O hc hm R hdiamond j i hne.symm s (-t)
    rw [weightCompanionWeyl_a2_X_swap_conjugate
      P b hdiamond O hc hm R i j hne hij hji (-t), neg_neg] at h
    exact h

/-- The two long positive families at a B2 edge commute. The proof derives
this from the checked mixed formula by a group cocycle, without division. -/
theorem weightCompanion_b2_long_positive_commute
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2)
    (s t : R) :
    Commute (weightCompanionX P b O hc hm R j s)
      (weightCompanionWeyl P b O hc hm R i 1 * weightCompanionX P b O hc hm R j t *
        (weightCompanionWeyl P b O hc hm R i 1)⁻¹) := by
  let ni := weightCompanionWeyl P b O hc hm R i 1
  let nj := weightCompanionWeyl P b O hc hm R j 1
  let y := weightCompanionXHom P b O hc hm R j
  let z := (MulAut.conj nj).toMonoidHom.comp
    ((weightCompanionXHom P b O hc hm R i).comp invMonoidHom)
  let w := (MulAut.conj ni).toMonoidHom.comp y
  have hy (a : R) : y (Multiplicative.ofAdd a) =
      weightCompanionX P b O hc hm R j a := rfl
  have hz (a : R) : z (Multiplicative.ofAdd a) =
      nj * weightCompanionX P b O hc hm R i (-a) * nj⁻¹ := rfl
  have hw (a : R) : w (Multiplicative.ofAdd a) =
      ni * weightCompanionX P b O hc hm R j a * ni⁻¹ := rfl
  have hcomm (a : Multiplicative R) :
      ⁅weightCompanionX P b O hc hm R i 1, y a⁆ = z a * w a := by
    change ⁅weightCompanionX P b O hc hm R i 1,
      y (Multiplicative.ofAdd a.toAdd)⁆ = z (Multiplicative.ofAdd a.toAdd) *
        w (Multiplicative.ofAdd a.toAdd)
    rw [hy, hz, hw]
    simpa only [one_pow, one_mul, neg_one_mul] using
      weightCompanionX_b2_commutator_eq_weyl_product
        P b hdiamond O hc hm R i j hne hij hji 1 a.toAdd
  have hzw (a c : Multiplicative R) : Commute (z a) (w c) := by
    have h := (weightCompanionX_commute_sameWeyl_conjugate_X
      P b O hc hm R hdiamond i j hne (-a.toAdd) c.toAdd).map
        (MulAut.conj nj).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [weightCompanionWeyl_b2_fixes_long_conjugate_X
      P b hdiamond O hc hm R i j hne hij hji c.toAdd] at h
    exact h
  have hyz (a c : Multiplicative R) : Commute (y a) (z c) :=
    weightCompanionX_commute_sameWeyl_conjugate_X
      P b O hc hm R hdiamond j i hne.symm a.toAdd (-c.toAdd)
  exact Atlas.GroupTheory.commute_of_commutator_hom_product y z w
    (weightCompanionX P b O hc hm R i 1) hcomm hzw hyz
      (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)

/-- All six unordered distinct positive pairs in B2. The families Z,V have
labels α+β and 2α+β; the short--short coefficient -2 is retained in characteristic two. -/
theorem weightCompanion_b2_positive_pairs
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2)
    (s t : R) :
    let X := weightCompanionX P b O hc hm R i
    let Y := weightCompanionX P b O hc hm R j
    let ni := weightCompanionWeyl P b O hc hm R i 1
    let nj := weightCompanionWeyl P b O hc hm R j 1
    let Z := fun a => nj * X a * nj⁻¹
    let V := fun a => ni * Y a * ni⁻¹
    ⁅X s, Y t⁆ = Z (-s * t) * V (s ^ 2 * t) ∧
    ⁅X s, Z t⁆ = V (-2 * s * t) ∧
    Commute (X s) (V t) ∧ Commute (Y s) (Z t) ∧
    Commute (Y s) (V t) ∧ Commute (Z s) (V t) := by
  refine ⟨weightCompanionX_b2_commutator_eq_weyl_product
    P b hdiamond O hc hm R i j hne hij hji s t,
    weightCompanionX_b2_short_short_commutator
    P b hdiamond O hc hm R i j hne hij hji s t, ?_, ?_, ?_, ?_⟩
  · exact weightCompanionX_commute_sameWeyl_conjugate_X
      P b O hc hm R hdiamond i j hne s t
  · exact weightCompanionX_commute_sameWeyl_conjugate_X
      P b O hc hm R hdiamond j i hne.symm s t
  · exact weightCompanion_b2_long_positive_commute
      P b hdiamond O hc hm R i j hne hij hji s t
  · have h := (weightCompanionX_commute_sameWeyl_conjugate_X
      P b O hc hm R hdiamond i j hne s t).map
        (MulAut.conj (weightCompanionWeyl P b O hc hm R j 1)).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [weightCompanionWeyl_b2_fixes_long_conjugate_X
      P b hdiamond O hc hm R i j hne hij hji t] at h
    exact h

end Atlas.Chevalley
