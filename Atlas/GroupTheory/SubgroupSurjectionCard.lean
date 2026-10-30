import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Ker

/-! A surjective homomorphism from a subgroup of a finite group to an equally
large group exhausts the ambient group. The homomorphism is an explicit input;
equal orders alone are not an identification. -/
noncomputable section
namespace Atlas.GroupTheory
variable {G K : Type*} [Group G] [Group K] [Finite G]

/-- The target need not carry a separate `Finite` instance: surjectivity from
the finite subgroup already supplies its finiteness. -/
theorem subgroup_eq_top_and_bijective_of_surjective_of_card
    (H : Subgroup G) (f : H →* K) (hf : Function.Surjective f)
    (hcard : Nat.card G = Nat.card K) :
    H = ⊤ ∧ Function.Bijective f := by
  have hc : Nat.card H = Nat.card K := le_antisymm
    (calc Nat.card H ≤ Nat.card G := H.card_le_card_group
          _ = Nat.card K := hcard)
    (Nat.card_le_card_of_surjective f hf)
  exact ⟨H.eq_top_of_card_eq (hc.trans hcard.symm),
    (Nat.bijective_iff_surjective_and_card f).mpr ⟨hf, hc⟩⟩

/-- The ambient equivalence extends the given subgroup homomorphism. -/
def subgroupSurjectionEquiv
    (H : Subgroup G) (f : H →* K) (hf : Function.Surjective f)
    (hcard : Nat.card G = Nat.card K) : G ≃* K :=
  (Subgroup.topEquiv.symm.trans
    (MulEquiv.subgroupCongr
      (subgroup_eq_top_and_bijective_of_surjective_of_card H f hf hcard).1).symm).trans
    (MulEquiv.ofBijective f
      (subgroup_eq_top_and_bijective_of_surjective_of_card H f hf hcard).2)

theorem subgroupSurjectionEquiv_apply
    (H : Subgroup G) (f : H →* K) (hf : Function.Surjective f)
    (hcard : Nat.card G = Nat.card K) (h : H) :
    subgroupSurjectionEquiv H f hf hcard h.val = f h := by
  change f ((MulEquiv.subgroupCongr
    (subgroup_eq_top_and_bijective_of_surjective_of_card H f hf hcard).1).symm
      (Subgroup.topEquiv.symm h.val)) = f h
  congr 1

end Atlas.GroupTheory
