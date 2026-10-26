import Atlas.LinearGroups.Orthogonal.Minus.RankThreeKernel
import Atlas.LinearGroups.Orthogonal.Minus.ProjectiveOrder
import Atlas.LinearGroups.Unitary.Order

/-! Full elementary image of the actual SU4 exterior action, retaining the central cover. -/
noncomputable section
open Classical
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem rankThree_elementary_kernel_card_le (hdeg : Module.finrank F K=2) :
    Nat.card (rankThreeElementaryHom hdeg).ker ≤ if (2:F)=0 then 1 else 2 := by
  classical
  have hs (g : (rankThreeElementaryHom hdeg).ker) :
      ∃a:K,a^2=1 ∧ g.val.val=a • (1:Matrix (Fin 4) (Fin 4) K) := by
    apply (rankThreeFullHom_eq_one_iff_scalar hdeg g.val).mp
    have hg : rankThreeElementaryHom hdeg g.val=1 := g.prop
    exact congrArg Subtype.val hg
  let p : (rankThreeElementaryHom hdeg).ker → {a:K // a^2=1} :=
    fun g => ⟨(hs g).choose,(hs g).choose_spec.1⟩
  have hp : Function.Injective p := by
    intro g h he
    have he' : (hs g).choose=(hs h).choose := congrArg Subtype.val he
    apply Subtype.ext
    apply Subtype.ext
    rw [(hs g).choose_spec.2,(hs h).choose_spec.2,he']
  have hcard := Nat.card_le_card_of_injective p hp
  rw [Atlas.Quadratic.card_squareOne] at hcard
  have ht : (2:K)=0 ↔ (2:F)=0 := by
    constructor
    · intro h
      apply (algebraMap F K).injective
      simpa only [map_ofNat, map_zero] using h
    · intro h
      have he := congrArg (algebraMap F K) h
      simpa only [map_ofNat, map_zero] using he
  simpa only [ht] using hcard

theorem rankThree_special_order_mul (hdeg : Module.finrank F K=2) :
    Nat.card (Atlas.Unitary.SU F K 4 hdeg)=
      Nat.card (E hdeg 2) * (if (2:F)=0 then 1 else 2) := by
  have hu := Atlas.Unitary.card_su_factor hdeg 4 (by decide)
  norm_num [Finset.prod_Icc_succ_top,Atlas.Unitary.orderFactor,Nat.even_iff] at hu
  by_cases h2 : (2:F)=0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    rw [ite_eq_left h2,mul_one,card_elementary_even hdeg 0,hu]
    norm_num [Finset.prod_range_succ]
    ring
  · rw [ite_eq_right h2,hu,card_elementary_odd_mul_two hdeg 0 h2]
    norm_num [Finset.prod_range_succ]
    ring

theorem rankThreeElementaryHom_surjective (hdeg : Module.finrank F K=2) :
    Function.Surjective (rankThreeElementaryHom hdeg) := by
  apply MonoidHom.surjective_of_card_ker_le_div
  rw [rankThree_special_order_mul hdeg,Nat.mul_div_cancel_left _ Nat.card_pos]
  exact rankThree_elementary_kernel_card_le hdeg

theorem rankThree_elementary_perfect (hdeg : Module.finrank F K=2) :
    Group.IsPerfect (E hdeg 2) := by
  letI := Atlas.Unitary.special_perfect_of_good hdeg
    (show Atlas.Unitary.Good 4 (Nat.card F) by simp [Atlas.Unitary.Good])
  exact Group.IsPerfect.ofSurjective (f := rankThreeElementaryHom hdeg)
    (rankThreeElementaryHom_surjective hdeg)
end Atlas.Orthogonal.Minus
