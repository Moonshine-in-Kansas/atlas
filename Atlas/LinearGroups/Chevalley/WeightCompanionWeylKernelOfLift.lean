import Atlas.LinearGroups.Chevalley.WeightCompanionWeylQuotientGeneration
import Atlas.LinearGroups.Chevalley.WeightCompanionFullWeylImage
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionLength

/-! The final algebraic implication from a homomorphic lift of actual simple
root reflections to actual simple Weyl cosets. The lift and its generator
equations remain explicit premises; their existence is not asserted here. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]




local instance kernelOfLiftTorusNormal : Subgroup.Normal ((Subgroup.subgroupOf (weightCompanionTorusSubgroup P b O hclosed hmin R) (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R))) :=
  weightCompanionTorusSubgroup_normal_extendedWeyl P b O hclosed hmin R




/-- The existing action, with its codomain changed along the already proved
equality of the simple-reflection subgroup and the full Weyl image. -/
def weightCompanionWeylQuotientFullAction : ((weightCompanionExtendedWeylSubgroup P b O hclosed hmin R) ⧸ ((Subgroup.subgroupOf (weightCompanionTorusSubgroup P b O hclosed hmin R) (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R)))) →* (P.weylGroupToPerm.range) :=
  (MulEquiv.subgroupCongr (simpleRootPermutationSubgroup_eq_weylImage P b)).toMonoidHom.comp
    (weightCompanionWeylQuotientAction P b O hclosed hmin R)

theorem weightCompanionWeylQuotientFullAction_simple (i : b.support) :
    weightCompanionWeylQuotientFullAction P b O hclosed hmin R
      (weightCompanionSimpleWeylCoset P b O hclosed hmin R i) =
        RootData.simpleWeylReflection P b i := by
  apply Subtype.ext
  change (weightCompanionWeylQuotientAction P b O hclosed hmin R
    (weightCompanionSimpleWeylCoset P b O hclosed hmin R i)).val = P.reflectionPerm i.val
  exact congrArg Subtype.val (weightCompanionWeylQuotientAction_simple P b O hclosed hmin R i)

theorem weightCompanionWeylQuotientFullAction_surjective :
    Function.Surjective (weightCompanionWeylQuotientFullAction P b O hclosed hmin R) :=
  (MulEquiv.subgroupCongr (simpleRootPermutationSubgroup_eq_weylImage P b)).surjective.comp
    (weightCompanionWeylQuotientAction_surjective P b O hclosed hmin R)

section Lift

variable (f : (P.weylGroupToPerm.range) →* ((weightCompanionExtendedWeylSubgroup P b O hclosed hmin R) ⧸ ((Subgroup.subgroupOf (weightCompanionTorusSubgroup P b O hclosed hmin R) (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R)))))
  (hf : ∀ i : b.support, f (RootData.simpleWeylReflection P b i) =
    weightCompanionSimpleWeylCoset P b O hclosed hmin R i)
include f hf

/-- Agreement on the actual generating cosets makes the lifted action the
identity. No injectivity hypothesis is used. -/
theorem weightCompanionWeylQuotient_leftInverse_of_lift :
    Function.LeftInverse f (weightCompanionWeylQuotientFullAction P b O hclosed hmin R) := by
  have hcomp : f.comp (weightCompanionWeylQuotientFullAction P b O hclosed hmin R) =
      MonoidHom.id ((weightCompanionExtendedWeylSubgroup P b O hclosed hmin R) ⧸ ((Subgroup.subgroupOf (weightCompanionTorusSubgroup P b O hclosed hmin R) (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R)))) := by
    apply MonoidHom.eq_of_eqOn_dense
      (weightCompanionSimpleWeylCoset_closure P b O hclosed hmin R)
    rintro q ⟨i, rfl⟩
    change f (weightCompanionWeylQuotientFullAction P b O hclosed hmin R
      (weightCompanionSimpleWeylCoset P b O hclosed hmin R i)) =
        weightCompanionSimpleWeylCoset P b O hclosed hmin R i
    rw [weightCompanionWeylQuotientFullAction_simple]
    exact hf i
  intro q
  exact congrArg (fun h : ((weightCompanionExtendedWeylSubgroup P b O hclosed hmin R) ⧸ ((Subgroup.subgroupOf (weightCompanionTorusSubgroup P b O hclosed hmin R) (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R)))) →* ((weightCompanionExtendedWeylSubgroup P b O hclosed hmin R) ⧸ ((Subgroup.subgroupOf (weightCompanionTorusSubgroup P b O hclosed hmin R) (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R)))) => h q) hcomp

theorem weightCompanionWeylQuotientFullAction_injective_of_lift :
    Function.Injective (weightCompanionWeylQuotientFullAction P b O hclosed hmin R) :=
  (weightCompanionWeylQuotient_leftInverse_of_lift P b O hclosed hmin R f hf).injective

/-- The original, unmodified quotient action is injective under the same
explicit lift premise. -/
theorem weightCompanionWeylQuotientAction_injective_of_lift :
    Function.Injective (weightCompanionWeylQuotientAction P b O hclosed hmin R) := by
  intro x y hxy
  apply weightCompanionWeylQuotientFullAction_injective_of_lift P b O hclosed hmin R f hf
  exact congrArg (MulEquiv.subgroupCongr (simpleRootPermutationSubgroup_eq_weylImage P b)) hxy

/-- Conditional converse to the previously proved torus-in-kernel inclusion.
The kernel here is the root-permutation action of the actual subgroup N. -/
theorem weightCompanionNRootPermHom_ker_eq_torus_of_lift :
    (weightCompanionNRootPermHom P b O hclosed hmin R).ker = ((Subgroup.subgroupOf (weightCompanionTorusSubgroup P b O hclosed hmin R) (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R))) := by
  apply le_antisymm
  · intro n hn
    apply (QuotientGroup.eq_one_iff n).mp
    apply weightCompanionWeylQuotientAction_injective_of_lift P b O hclosed hmin R f hf
    rw [map_one]
    apply Subtype.ext
    change weightCompanionNRootPermHom P b O hclosed hmin R n = 1
    exact hn
  · exact weightCompanionTorus_le_rootPermKer P b O hclosed hmin R

/-- Conditional isomorphism from the literal quotient N/T to the actual Weyl
image, using the original quotient action as its underlying map. -/
def weightCompanionWeylQuotientEquiv_of_lift : ((weightCompanionExtendedWeylSubgroup P b O hclosed hmin R) ⧸ ((Subgroup.subgroupOf (weightCompanionTorusSubgroup P b O hclosed hmin R) (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R)))) ≃* (P.weylGroupToPerm.range) :=
  MulEquiv.ofBijective (weightCompanionWeylQuotientFullAction P b O hclosed hmin R)
    ⟨weightCompanionWeylQuotientFullAction_injective_of_lift P b O hclosed hmin R f hf,
      weightCompanionWeylQuotientFullAction_surjective P b O hclosed hmin R⟩

theorem weightCompanionWeylQuotientEquiv_of_lift_apply (q : ((weightCompanionExtendedWeylSubgroup P b O hclosed hmin R) ⧸ ((Subgroup.subgroupOf (weightCompanionTorusSubgroup P b O hclosed hmin R) (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R))))) :
    weightCompanionWeylQuotientEquiv_of_lift P b O hclosed hmin R f hf q =
      weightCompanionWeylQuotientFullAction P b O hclosed hmin R q := rfl

end Lift
end Atlas.Chevalley
