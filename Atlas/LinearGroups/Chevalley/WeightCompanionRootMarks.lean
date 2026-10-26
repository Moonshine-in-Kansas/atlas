import Atlas.GroupTheory.LabelledSubgroupMarks
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylSquare
import Atlas.LinearGroups.Chevalley.WeightCompanionCrossTorus

/-! The actual simple-root subgroup together with its root label. Permutation
and group components are recorded separately, so this bookkeeping does not
require a nontrivial coefficient ring or an injective adjoint projection. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Integral Integral.Minuscule Atlas.GroupTheory

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

def weightCompanionSimpleRootMark (i : b.support) :
    ι × Subgroup (WeightCompanion P b O hc hm R) :=
  (i.val, (weightCompanionXHom P b O hc hm R i).range)

def weightCompanionMarkedWeyl (i : b.support) :
    Equiv.Perm ι × WeightCompanion P b O hc hm R :=
  (P.reflectionPerm i.val, weightCompanionWeyl P b O hc hm R i 1)

/-- This is the generic prefix-mark construction applied to literal matrices
and literal reflection permutations, not a replacement group construction. -/
def weightCompanionMarkedWordSet (l : List b.support) :
    Set (ι × Subgroup (WeightCompanion P b O hc hm R)) :=
  ReducedWords.markedWordSet (weightCompanionMarkedWeyl P b O hc hm R)
    labelledSubgroupAction (weightCompanionSimpleRootMark P b O hc hm R) l

/-- The square of any simple Weyl lift preserves every simple-root subgroup.
The action on its parameter is multiplication by an explicit unit. -/
theorem weightCompanionSimpleRootMark_weyl_square (i j : b.support) :
    labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
      (labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
        (weightCompanionSimpleRootMark P b O hc hm R j)) =
      weightCompanionSimpleRootMark P b O hc hm R j := by
  apply Prod.ext
  · exact P.reflectionPerm_self i.val j.val
  · change conjugateSubgroup (weightCompanionWeyl P b O hc hm R i 1)
        (conjugateSubgroup (weightCompanionWeyl P b O hc hm R i 1)
          (weightCompanionXHom P b O hc hm R j).range) =
      (weightCompanionXHom P b O hc hm R j).range
    rw [← conjugateSubgroup_mul, ← pow_two, weightCompanionWeyl_one_sq]
    let a : Rˣ := (-1) ^ b.cartanMatrix j i
    let e : Multiplicative R → Multiplicative R :=
      fun x => Multiplicative.ofAdd (a.val * x.toAdd)
    have he : Function.Surjective e := by
      intro x
      refine ⟨Multiplicative.ofAdd (a.inv * x.toAdd), ?_⟩
      change a.val * (a.inv * x.toAdd) = x.toAdd
      rw [← mul_assoc, a.val_inv, one_mul]
    apply conjugateSubgroup_range_eq_of_surjective _ _ _ e he
    intro x
    exact weightCompanionTorus_conjugate_X_cross P b O hc hm R j i (-1) x.toAdd

end Atlas.Chevalley
