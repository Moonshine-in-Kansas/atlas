import Atlas.LinearGroups.Chevalley.WeightCompanionA2Commutator
import Mathlib.GroupTheory.IsPerfect

/-! Perfectness from actual simultaneous A2 commutators in every commutative ring.
The two root families are treated separately; the adjoint projection is not used
to lift perfectness. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Group Integral Integral.Minuscule
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

theorem weightCompanionX_mem_commutator_of_a2_neighbour
    (i j : b.support) (hne : j ≠ i)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (t : R) :
    weightCompanionX P b O hc hm R i t ∈ commutator (WeightCompanion P b O hc hm R) := by
  have hpin := weightCompanionX_a2_commutator_eq_weyl_conjugate
    P b hdiamond O hc hm R j i hne hji hij 1 t
  simp only [one_mul] at hpin
  have hconj : weightCompanionWeyl P b O hc hm R j 1 *
      weightCompanionX P b O hc hm R i t * (weightCompanionWeyl P b O hc hm R j 1)⁻¹ ∈
        commutator (WeightCompanion P b O hc hm R) := by
    rw [← hpin]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hrot : (weightCompanionWeyl P b O hc hm R j 1)⁻¹ *
      (weightCompanionWeyl P b O hc hm R j 1 * weightCompanionX P b O hc hm R i t) ∈
        commutator (WeightCompanion P b O hc hm R) :=
    (inferInstance : (commutator (WeightCompanion P b O hc hm R)).Normal).mem_comm hconj
  simpa only [inv_mul_cancel_left] using hrot

theorem weightCompanionY_mem_commutator_of_a2_neighbour
    (i j : b.support) (hne : j ≠ i)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (t : R) :
    weightCompanionY P b O hc hm R i t ∈ commutator (WeightCompanion P b O hc hm R) := by
  let V := weightCompanionY P b O hc hm R j 1 *
    weightCompanionX P b O hc hm R j (-1) * weightCompanionY P b O hc hm R j 1
  have hpin := weightCompanionY_a2_commutator_eq_negative_weyl_conjugate
    P b hdiamond O hc hm R j i hne hji hij 1 t
  simp only [one_mul] at hpin
  change ⁅weightCompanionY P b O hc hm R j 1, weightCompanionY P b O hc hm R i t⁆ =
    V * weightCompanionY P b O hc hm R i t * V⁻¹ at hpin
  have hconj : V * weightCompanionY P b O hc hm R i t * V⁻¹ ∈
      commutator (WeightCompanion P b O hc hm R) := by
    rw [← hpin]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hrot : V⁻¹ * (V * weightCompanionY P b O hc hm R i t) ∈
      commutator (WeightCompanion P b O hc hm R) :=
    (inferInstance : (commutator (WeightCompanion P b O hc hm R)).Normal).mem_comm hconj
  simpa only [inv_mul_cancel_left] using hrot

/-- All-ring perfectness of the actual companion under an actual Cartan
single-edge-neighbour condition. No condition on the full projection kernel. -/
theorem weightCompanion_isPerfect_of_a2_neighbours
    (hrows : ∀ i : b.support, ∃ j : b.support, j ≠ i ∧
      b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -1) :
    IsPerfect (WeightCompanion P b O hc hm R) := by
  apply isPerfect_def.mpr
  apply top_unique
  intro g hg
  apply weightCompanion_induction P b O hc hm R ?_ ?_ (commutator _).one_mem
    (fun _ _ => (commutator _).mul_mem) (fun _ => (commutator _).inv_mem) g
  · intro i t
    obtain ⟨j, hne, hij, hji⟩ := hrows i
    exact weightCompanionX_mem_commutator_of_a2_neighbour
      P b hdiamond O hc hm R i j hne hij hji t
  · intro i t
    obtain ⟨j, hne, hij, hji⟩ := hrows i
    exact weightCompanionY_mem_commutator_of_a2_neighbour
      P b hdiamond O hc hm R i j hne hij hji t

end Atlas.Chevalley
