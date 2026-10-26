import Atlas.LinearGroups.Triality.RankOneGenerators
import Atlas.LinearGroups.Elementary
import Atlas.LinearGroups.SL2Perfect

/-! The short SL₂ map lands in the literal group and its image is perfect. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal Matrix
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem rankOneShortOrthogonal_mem (g : SpecialLinearGroup (Fin 2) K) :
    rankOneShortOrthogonal F K g ∈ generated F K := by
  apply Atlas.sl_elementary_induction
    (fun g => rankOneShortOrthogonal F K g ∈ generated F K) _ _ g
  · intro i j hij a
    fin_cases i <;> fin_cases j <;> try contradiction
    · rw [rankOneShortOrthogonal_upper]
      exact shortRoot_mem F K a
    · rw [rankOneShortOrthogonal_lower]
      exact shortNegativeRoot_mem F K a
  · intro g h hg hh
    rw [map_mul]
    exact Subgroup.mul_mem _ hg hh

def rankOneShort : SpecialLinearGroup (Fin 2) K →* Group F K :=
  (rankOneShortOrthogonal F K).codRestrict (generated F K) (rankOneShortOrthogonal_mem F K)

theorem cubic_sl_two_perfect (hdeg : Module.finrank F K = 3) :
    _root_.Group.IsPerfect (SpecialLinearGroup (Fin 2) K) := by
  apply Atlas.sl_two_perfect_of_four_le_card
  rw [FiniteCubic.card_extension hdeg]
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  exact le_trans (by norm_num : 4 ≤ 2^3) (Nat.pow_le_pow_left hq 3)

theorem rankOneShort_range_perfect (hdeg : Module.finrank F K = 3) :
    _root_.Group.IsPerfect (rankOneShort F K).range := by
  letI := cubic_sl_two_perfect F K hdeg
  exact _root_.Group.IsPerfect.range _

theorem rankOneShort_range_le_commutator (hdeg : Module.finrank F K = 3) :
    (rankOneShort F K).range ≤ commutator (Group F K) := by
  letI := rankOneShort_range_perfect F K hdeg
  have h : ⁅(rankOneShort F K).range,(rankOneShort F K).range⁆ ≤ commutator (Group F K) :=
    Subgroup.commutator_mono le_top le_top
  simpa only [Subgroup.commutator_eq_self] using h

theorem shortRoot_mem_commutator (hdeg : Module.finrank F K = 3) (a : K) :
    (⟨shortRoot F K a,shortRoot_mem F K a⟩ : Group F K) ∈ commutator (Group F K) := by
  apply rankOneShort_range_le_commutator F K hdeg
  refine ⟨SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) a, ?_⟩
  apply Subtype.ext
  exact rankOneShortOrthogonal_upper F K a

theorem shortNegativeRoot_mem_commutator (hdeg : Module.finrank F K = 3) (a : K) :
    (⟨shortNegativeRoot F K a,shortNegativeRoot_mem F K a⟩ : Group F K) ∈ commutator (Group F K) := by
  apply rankOneShort_range_le_commutator F K hdeg
  refine ⟨SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) a, ?_⟩
  apply Subtype.ext
  exact rankOneShortOrthogonal_lower F K a

end Atlas.Triality
