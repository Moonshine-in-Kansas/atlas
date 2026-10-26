import Atlas.LinearGroups.Chevalley.PositiveWitnessedOvergroupDescent
import Atlas.LinearGroups.Chevalley.RootData.ReducedWordFirstDescent

/-! Every letter of a reduced Weyl word is detected inside an overgroup of B
containing any actual N lift of that word. The lift need not be canonical,
and neither a diamond premise nor a field hypothesis is needed. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

/-- An actual N element in H forces every simple Tits representative occurring
in any reduced word for its root permutation into H. -/
theorem weightCompanionWeyl_mem_of_reduced_word_lift_mem
    (H : Subgroup (WeightCompanion P b O hc hm R))
    (hB : positiveWitnessedTorusJoin P b O hc hm R ≤ H)
    (l : List b.support) (hred : IsReducedRootWord P b l)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (hn : n.val ∈ H)
    (hperm : weightCompanionNRootPermHom P b O hc hm R n =
      (rootWeylWord P b l).val) :
    ∀ i ∈ l, weightCompanionWeyl P b O hc hm R i 1 ∈ H := by
  induction l generalizing n with
  | nil => simp
  | cons i l ih =>
    have hneg : ¬ b.IsPos
        (weightCompanionNRootPermHom P b O hc hm R n⁻¹ i.val) := by
      rw [map_inv, hperm]
      exact rootWeylWord_inverse_first_negative P b i l hred
    have hi := weightCompanionWeyl_mem_of_inverse_root_negative
      P b O hc hm R H hB n hn i hneg
    let m : weightCompanionExtendedWeylSubgroup P b O hc hm R :=
      (weightCompanionSimpleWeylInN P b O hc hm R i)⁻¹ * n
    have hmH : m.val ∈ H :=
      H.mul_mem (H.inv_mem hi) hn
    have hmperm : weightCompanionNRootPermHom P b O hc hm R m =
        (rootWeylWord P b l).val := by
      dsimp only [m]
      rw [map_mul, map_inv, weightCompanionNRootPermHom_simple, hperm]
      change (P.reflectionPerm i.val)⁻¹ *
        (P.reflectionPerm i.val * (rootWeylWord P b l).val) = _
      exact inv_mul_cancel_left _ _
    have htail : IsReducedRootWord P b l := by
      have ht := isReducedRootWord_drop P b (i :: l) hred 1
      change IsReducedRootWord P b l at ht
      exact ht
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · exact ih (hred := htail) (n := m) hmH hmperm j hj

end Atlas.Chevalley
