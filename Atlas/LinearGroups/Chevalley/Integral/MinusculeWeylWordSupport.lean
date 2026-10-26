import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeylBraidA2
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionExchange

/-! Actual weight-reflection words and their signed minuscule matrix action.
The inverse support uses the actual inverse unit, not a reversed positive word. -/

noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- The actual integral linear action of the chosen simple-reflection word. -/
def weightReflectionWord (l : List b.support) : Module.End ℤ (WeightLattice P) :=
  (l.map (fun i => weightReflection P i.val)).prod

theorem weightReflectionWord_rootWeight (l : List b.support) (β : ι) :
    weightReflectionWord P b l (rootWeight P β) =
      rootWeight P (RootData.simpleReflectionWord P b l β) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change weightReflection P i.val (weightReflectionWord P b l (rootWeight P β)) = _
    rw [ih, weightReflection_rootWeight]
    rfl

variable (S : Finset (WeightLattice P))
  (hc : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)

/-- The same word on the literal finite orbit of weights. -/
def weightOrbitReflectionWord (l : List b.support) : Equiv.Perm (WeightOrbit P S) :=
  (l.map (fun i => weightOrbitReflection P S hc i.val)).prod

theorem weightOrbitReflectionWord_val (l : List b.support) (μ : WeightOrbit P S) :
    (weightOrbitReflectionWord P b S hc l μ).val =
      weightReflectionWord P b l μ.val := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change weightReflection P i.val (weightOrbitReflectionWord P b S hc l μ).val =
      weightReflection P i.val (weightReflectionWord P b l μ.val)
    rw [ih]

variable
  (hm : ∀ μ ∈ S, ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

/-- A literal product of the previously constructed minuscule Weyl operators. -/
def weightOrbitWeylWordEquiv (l : List b.support) :
    (WeightOrbit P S →₀ R) ≃ₗ[R] (WeightOrbit P S →₀ R) :=
  (l.map (fun i => (stringsOfWeightOrbit P S hc hm).weylEquiv R i.val 1)).prod

/-- The coefficient is a product of the actual ±1 factors, retained as a unit. -/
def weightOrbitWeylWordSign : List b.support → WeightOrbit P S → Rˣ
  | [], _ => 1
  | i :: l, μ =>
      (if (weightOrbitReflectionWord P b S hc l μ).val (corootElement P i.val) = 1
        then -1 else 1) * weightOrbitWeylWordSign l μ

/-- Full signed action, with no nontriviality or field assumption on R. -/
theorem weightOrbitWeylWordEquiv_single (l : List b.support)
    (μ : WeightOrbit P S) (r : R) :
    weightOrbitWeylWordEquiv P b S hc hm R l (Finsupp.single μ r) =
      Finsupp.single (weightOrbitReflectionWord P b S hc l μ)
        ((weightOrbitWeylWordSign P b S hc R l μ).val * r) := by
  induction l with
  | nil => simp [weightOrbitWeylWordEquiv, weightOrbitReflectionWord,
      weightOrbitWeylWordSign]
  | cons i l ih =>
    change (stringsOfWeightOrbit P S hc hm).weylEquiv R i.val 1
      (weightOrbitWeylWordEquiv P b S hc hm R l (Finsupp.single μ r)) = _
    rw [ih, weightOrbit_weyl_one_single_signed]
    change Finsupp.single
      (weightOrbitReflection P S hc i.val (weightOrbitReflectionWord P b S hc l μ))
      ((if (weightOrbitReflectionWord P b S hc l μ).val (corootElement P i.val) = 1
        then (-1 : R) else 1) *
          ((weightOrbitWeylWordSign P b S hc R l μ).val * r)) = _
    simp only [weightOrbitWeylWordSign, Units.val_mul,
      weightOrbitReflectionWord, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    split_ifs with h <;> simp only [h, ite_true, ite_false, Units.val_neg, Units.val_one, mul_assoc]

/-- The actual matrix unit associated with that literal word. -/
def weightOrbitWeylWord (l : List b.support) :
    (Matrix (WeightOrbit P S) (WeightOrbit P S) R)ˣ :=
  Strings.equivMatrixHom R (weightOrbitWeylWordEquiv P b S hc hm R l)

@[simp] theorem weightOrbitWeylWord_nil :
    weightOrbitWeylWord P b S hc hm R [] = 1 := by
  simp [weightOrbitWeylWord, weightOrbitWeylWordEquiv]

@[simp] theorem weightOrbitWeylWord_cons (i : b.support) (l : List b.support) :
    weightOrbitWeylWord P b S hc hm R (i :: l) =
      (stringsOfWeightOrbit P S hc hm).weylMatrixUnit R i.val 1 *
        weightOrbitWeylWord P b S hc hm R l := by
  simp only [weightOrbitWeylWord, weightOrbitWeylWordEquiv, List.map_cons,
    List.prod_cons, map_mul, Strings.equivMatrixHom_weyl]

/-- Explicit matrix column, including its actual unit sign. -/
theorem weightOrbitWeylWord_entry (l : List b.support) (μ ν : WeightOrbit P S) :
    (weightOrbitWeylWord P b S hc hm R l).val μ ν =
      if weightOrbitReflectionWord P b S hc l ν = μ
      then (weightOrbitWeylWordSign P b S hc R l ν).val else 0 := by
  change LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
    (weightOrbitWeylWordEquiv P b S hc hm R l).toLinearMap μ ν = _
  rw [LinearMap.toMatrix_apply]
  change weightOrbitWeylWordEquiv P b S hc hm R l (Finsupp.single ν 1) μ = _
  rw [weightOrbitWeylWordEquiv_single]
  simp only [mul_one, Finsupp.single_apply]

/-- A nonzero matrix entry lies on the graph of the actual weight permutation. -/
theorem weightOrbitWeylWord_support (l : List b.support) (μ ν : WeightOrbit P S)
    (hne : (weightOrbitWeylWord P b S hc hm R l).val μ ν ≠ 0) :
    μ = weightOrbitReflectionWord P b S hc l ν := by
  rw [weightOrbitWeylWord_entry] at hne
  by_contra h
  exact hne (if_neg (Ne.symm h))

/-- Actual inverse operator formula. The root-word signs are not discarded. -/
theorem weightOrbitWeylWordEquiv_inv_single (l : List b.support)
    (μ : WeightOrbit P S) (r : R) :
    (weightOrbitWeylWordEquiv P b S hc hm R l).symm (Finsupp.single μ r) =
      Finsupp.single ((weightOrbitReflectionWord P b S hc l)⁻¹ μ)
        (((weightOrbitWeylWordSign P b S hc R l
          ((weightOrbitReflectionWord P b S hc l)⁻¹ μ))⁻¹).val * r) := by
  apply (weightOrbitWeylWordEquiv P b S hc hm R l).injective
  rw [LinearEquiv.apply_symm_apply, weightOrbitWeylWordEquiv_single]
  have hlabel : weightOrbitReflectionWord P b S hc l
      ((weightOrbitReflectionWord P b S hc l)⁻¹ μ) = μ := by
    rw [Equiv.Perm.inv_def]
    exact (weightOrbitReflectionWord P b S hc l).apply_symm_apply μ
  rw [hlabel]
  simp only [← mul_assoc, Units.mul_inv, one_mul]

/-- The inverse matrix support follows from the actual inverse linear operator. -/
theorem weightOrbitWeylWord_inv_support (l : List b.support)
    (μ ν : WeightOrbit P S)
    (hne : ((weightOrbitWeylWord P b S hc hm R l)⁻¹).val μ ν ≠ 0) :
    μ = (weightOrbitReflectionWord P b S hc l)⁻¹ ν := by
  have hmapped : (weightOrbitWeylWord P b S hc hm R l)⁻¹ =
      Strings.equivMatrixHom R (weightOrbitWeylWordEquiv P b S hc hm R l).symm := by
    change (Strings.equivMatrixHom R
      (weightOrbitWeylWordEquiv P b S hc hm R l))⁻¹ = _
    rw [← map_inv]
    rfl
  rw [hmapped] at hne
  change (LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
    (weightOrbitWeylWordEquiv P b S hc hm R l).symm.toLinearMap) μ ν ≠ 0 at hne
  rw [LinearMap.toMatrix_apply] at hne
  change (weightOrbitWeylWordEquiv P b S hc hm R l).symm (Finsupp.single ν 1) μ ≠ 0 at hne
  rw [weightOrbitWeylWordEquiv_inv_single] at hne
  by_contra h
  exact hne (by simp only [Finsupp.single_apply, if_neg (Ne.symm h)])

end Atlas.Chevalley.Integral.Minuscule
