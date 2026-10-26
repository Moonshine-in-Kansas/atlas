import Atlas.Tits.TransferEvaluation
import Atlas.Tits.TransferKernelConsequences

/-! Order and kernel identification for the actual derived cross stabilizer.
These statements have no unresolved transfer or simplicity hypothesis. -/
namespace Atlas.Tits

instance derivedNormal : derivedSubgroup.Normal :=
  inferInstanceAs (commutator Ambient).Normal

theorem transfer_nontrivial : ∃g : Ambient, transfer g ≠ 1 :=
  transfer_nontrivial_of_alpha transfer_alpha

theorem derived_eq_transferKernel : derivedSubgroup = transfer.ker :=
  derived_eq_transferKernel_of_transfer_alpha transfer_alpha

theorem index_derived : derivedSubgroup.index = 2 :=
  derived_index_two_of_transfer_alpha transfer_alpha

theorem card : Nat.card Model = 17971200 :=
  model_order_of_transfer_alpha transfer_alpha

theorem transfer_range_order : Nat.card transfer.range = 2 :=
  transfer_range_order_of_alpha transfer_alpha

theorem normal_subgroups (N : Subgroup Ambient) (hN : N.Normal) :
    N = ⊥ ∨ N = derivedSubgroup ∨ N = ⊤ :=
  ambient_normal_classification_of_transfer_alpha transfer_alpha N hN

instance modelNontrivial : Nontrivial Model :=
  Finite.one_lt_card_iff_nontrivial.mp (by rw [card]; decide)

theorem derived_ne_bot : derivedSubgroup ≠ ⊥ := by
  intro h
  have hc := card
  change Nat.card derivedSubgroup = 17971200 at hc
  rw [h,Subgroup.card_bot] at hc
  contradiction

end Atlas.Tits
