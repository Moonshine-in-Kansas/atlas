import Atlas.LinearGroups.Chevalley.WeightCompanionPerfectnessA2
import Atlas.LinearGroups.Chevalley.WeightCompanionDoubleEdgeCommutator
import Atlas.GroupTheory.DoubleEdgeNormalPropagation

/-! All-ring perfectness from actual single-edge seeds and double-edge
propagation in the simultaneous companion. Positive and negative generators
are treated separately on the same actual weight blocks. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Group Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]
  (hcover : ∀ i : b.support,
    (∃ j : b.support, j ≠ i ∧ b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -1) ∨
    (∃ j k : b.support, j ≠ i ∧ k ≠ j ∧
      b.cartanMatrix j k = -1 ∧ b.cartanMatrix k j = -1 ∧
      ((b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -2) ∨
       (b.cartanMatrix i j = -2 ∧ b.cartanMatrix j i = -1))))

include hdiamond hcover

/-- Each positive family is seeded by an actual A2 neighbour or reached
from such a seed by the actual mixed double-edge group word. -/
theorem weightCompanionX_mem_commutator_of_a2_double_cover
    (i : b.support) (t : R) :
    weightCompanionX P b O hc hm R i t ∈ commutator (WeightCompanion P b O hc hm R) := by
  rcases hcover i with ⟨j, hne, hij, hji⟩ | ⟨j, k, hji, hkj, hjk, hkj', hedge⟩
  · exact weightCompanionX_mem_commutator_of_a2_neighbour
      P b hdiamond O hc hm R i j hne hij hji t
  · have hj (s : R) : weightCompanionX P b O hc hm R j s ∈
        commutator (WeightCompanion P b O hc hm R) :=
      weightCompanionX_mem_commutator_of_a2_neighbour
        P b hdiamond O hc hm R j k hkj hjk hkj' s
    rcases hedge with ⟨hij, hji'⟩ | ⟨hij, hji'⟩
    · exact Atlas.GroupTheory.short_family_mem_normal_of_long_of_mixed_relation
        (commutator (WeightCompanion P b O hc hm R))
        (weightCompanionX P b O hc hm R i) (weightCompanionX P b O hc hm R j)
        (weightCompanionWeyl P b O hc hm R i 1) (weightCompanionWeyl P b O hc hm R j 1)
        (weightCompanionX_b2_commutator_eq_weyl_product
          P b hdiamond O hc hm R i j hji.symm hij hji') hj t
    · exact Atlas.GroupTheory.long_family_mem_normal_of_short_of_mixed_relation
        (commutator (WeightCompanion P b O hc hm R))
        (weightCompanionX P b O hc hm R j) (weightCompanionX P b O hc hm R i)
        (weightCompanionWeyl P b O hc hm R j 1) (weightCompanionWeyl P b O hc hm R i 1)
        (weightCompanionX_b2_commutator_eq_weyl_product
          P b hdiamond O hc hm R j i hji hji' hij) hj t

/-- Negative families use their separately proved actual word. No global
companion opposition, weight-negation closure or projection injectivity is used. -/
theorem weightCompanionY_mem_commutator_of_a2_double_cover
    (i : b.support) (t : R) :
    weightCompanionY P b O hc hm R i t ∈ commutator (WeightCompanion P b O hc hm R) := by
  let V (k : b.support) := weightCompanionY P b O hc hm R k 1 *
    weightCompanionX P b O hc hm R k (-1) * weightCompanionY P b O hc hm R k 1
  rcases hcover i with ⟨j, hne, hij, hji⟩ | ⟨j, k, hji, hkj, hjk, hkj', hedge⟩
  · exact weightCompanionY_mem_commutator_of_a2_neighbour
      P b hdiamond O hc hm R i j hne hij hji t
  · have hj (s : R) : weightCompanionY P b O hc hm R j s ∈
        commutator (WeightCompanion P b O hc hm R) :=
      weightCompanionY_mem_commutator_of_a2_neighbour
        P b hdiamond O hc hm R j k hkj hjk hkj' s
    rcases hedge with ⟨hij, hji'⟩ | ⟨hij, hji'⟩
    · exact Atlas.GroupTheory.short_family_mem_normal_of_long_of_mixed_relation
        (commutator (WeightCompanion P b O hc hm R))
        (weightCompanionY P b O hc hm R i) (weightCompanionY P b O hc hm R j)
        (V i) (V j)
        (weightCompanionY_b2_commutator_eq_negative_weyl_product
          P b hdiamond O hc hm R i j hji.symm hij hji') hj t
    · exact Atlas.GroupTheory.long_family_mem_normal_of_short_of_mixed_relation
        (commutator (WeightCompanion P b O hc hm R))
        (weightCompanionY P b O hc hm R j) (weightCompanionY P b O hc hm R i)
        (V j) (V i)
        (weightCompanionY_b2_commutator_eq_negative_weyl_product
          P b hdiamond O hc hm R j i hji hji' hij) hj t

/-- Perfectness of the actual simultaneous subgroup under the explicit
Cartan cover. The complete positive and negative generating families lie
in its own commutator subgroup; perfectness is not lifted from a quotient. -/
theorem weightCompanion_isPerfect_of_a2_double_cover :
    IsPerfect (WeightCompanion P b O hc hm R) := by
  apply isPerfect_def.mpr
  apply top_unique
  intro g hg
  exact weightCompanion_induction P b O hc hm R
    (weightCompanionX_mem_commutator_of_a2_double_cover P b hdiamond O hc hm R hcover)
    (weightCompanionY_mem_commutator_of_a2_double_cover P b hdiamond O hc hm R hcover)
    (commutator _).one_mem
    (fun _ _ => (commutator _).mul_mem) (fun _ => (commutator _).inv_mem) g

end Atlas.Chevalley
