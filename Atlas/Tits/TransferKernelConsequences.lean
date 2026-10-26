import Atlas.Tits.TransferDefinition
import Atlas.Tits.TransferWitnessPowers
import Atlas.Tits.OddRelations
import Atlas.GroupTheory.DerivedIndexTwoKernel
import Atlas.Tits.OrderArithmetic

/-! Consequences for the actual derived subgroup, conditional only on the
 pending evaluation of the actual transfer on alpha. No simplicity premise
 enters the kernel identification or order calculation. -/
namespace Atlas.Tits
open Atlas.GroupTheory

 theorem transfer_nontrivial_of_alpha (hα : transfer localAlpha = -1) :
    ∃g : Ambient, transfer g ≠ 1 := by
  refine ⟨localAlpha,?_⟩
  rw [hα]
  decide

/-- The actual derived subgroup is the actual transfer kernel. -/
theorem derived_eq_transferKernel_of_transfer_alpha (hα : transfer localAlpha = -1) :
    derivedSubgroup = transfer.ker := by
  exact (commutator_eq_ker_and_index_two ambient_nonabelian
    (fun N hN hne => by letI := hN; exact normal_index_le_two N hne)
    transfer (transfer_nontrivial_of_alpha hα)).1

theorem derived_index_two_of_transfer_alpha (hα : transfer localAlpha = -1) :
    derivedSubgroup.index = 2 := by
  exact (commutator_eq_ker_and_index_two ambient_nonabelian
    (fun N hN hne => by letI := hN; exact normal_index_le_two N hne)
    transfer (transfer_nontrivial_of_alpha hα)).2

/-- Order certificate for the original Model, the derived subgroup of the
 inherited Rudvalis cross stabilizer. This proof does not use simplicity. -/
theorem model_order_of_transfer_alpha (hα : transfer localAlpha = -1) :
    Nat.card Model = 17971200 := by
  have h := derivedSubgroup.card_mul_index
  rw [derived_index_two_of_transfer_alpha hα,cardAmbient] at h
  change Nat.card derivedSubgroup = 17971200
  omega

theorem transfer_range_order_of_alpha (hα : transfer localAlpha = -1) :
    Nat.card transfer.range = 2 :=
  character_range_card_two ambient_nonabelian
    (fun N hN hne => by letI := hN; exact normal_index_le_two N hne)
    transfer (transfer_nontrivial_of_alpha hα)

/-- Every nontrivial ambient normal subgroup contains the actual derived subgroup. -/
theorem ambient_normal_contains_derived (N : Subgroup Ambient) (hN : N.Normal) :
    N = ⊥ ∨ derivedSubgroup ≤ N :=
  commutator_normal_dichotomy_of_index_bound
    (fun N hN hne => by letI := hN; exact normal_index_le_two N hne) N hN

/-- The ambient normal-subgroup list is obtained without assuming simplicity
 of the derived subgroup. -/
theorem ambient_normal_classification_of_transfer_alpha
    (hα : transfer localAlpha = -1) (N : Subgroup Ambient) (hN : N.Normal) :
    N = ⊥ ∨ N = derivedSubgroup ∨ N = ⊤ := by
  rcases ambient_normal_contains_derived N hN with hb | hle
  · exact Or.inl hb
  right
  by_cases ht : N = ⊤
  · exact Or.inr ht
  left
  by_contra hn
  have hs := Subgroup.index_strictAnti (lt_of_le_of_ne hle (Ne.symm hn))
  rw [derived_index_two_of_transfer_alpha hα] at hs
  have hl := N.one_lt_index_of_ne_top ht
  omega

end Atlas.Tits
