import Mathlib.GroupTheory.DoubleCoset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-! A double coset of an element normalizing B has exactly the cardinality
of B. This does not require the ambient group or B to be finite. -/
noncomputable section
namespace Atlas.GroupTheory
variable {G : Type*} [Group G] (B : Subgroup G) (z : G)

def doubleCosetNormalizerEquiv (hz : z ∈ Subgroup.normalizer B) :
    B ≃ DoubleCoset.doubleCoset z B B := by
  let f : B → DoubleCoset.doubleCoset z B B := fun b =>
    ⟨b.val * z, DoubleCoset.mem_doubleCoset.mpr
      ⟨b.val, b.property, 1, B.one_mem, (mul_one _).symm⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    apply Subtype.ext
    exact mul_right_cancel (congrArg Subtype.val h)
  · intro x
    obtain ⟨a, ha, c, hc, he⟩ := DoubleCoset.mem_doubleCoset.mp x.property
    have hzc : z * c * z⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp hz c).mp hc
    refine ⟨⟨a * (z * c * z⁻¹), B.mul_mem ha hzc⟩, ?_⟩
    apply Subtype.ext
    change (a * (z * c * z⁻¹)) * z = x.val
    rw [he]
    group

theorem doubleCoset_card_of_mem_normalizer (hz : z ∈ Subgroup.normalizer B) :
    Nat.card (DoubleCoset.doubleCoset z B B) = Nat.card B :=
  (Nat.card_congr (doubleCosetNormalizerEquiv B z hz)).symm

end Atlas.GroupTheory
