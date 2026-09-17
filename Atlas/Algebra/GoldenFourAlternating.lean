import Atlas.Algebra.IcosianNormOneReductionSurjective
import Atlas.LinearGroups.PSLFamily
import Mathlib.GroupTheory.SpecificGroups.Alternating

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped MatrixGroups LinearAlgebra.Projectivization
attribute [local instance] Classical.propDecidable

theorem goldenFour_SL_center : Subgroup.center (SL(2,GoldenFour))=⊥ := by
  rw [Subgroup.eq_bot_iff_card]
  rw [Atlas.card_sl_center]
  have hc : Nat.card GoldenFour=4 := by rw [Nat.card_eq_fintype_card,goldenFour_card]
  rw [hc]
  norm_num

/-- The canonical central quotient is an isomorphism in dimension two over F4. -/
def goldenFourSLPSL : SL(2,GoldenFour) ≃* PSL(2,GoldenFour) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center (SL(2,GoldenFour))))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',goldenFour_SL_center]),
      QuotientGroup.mk'_surjective _⟩

theorem goldenFour_PSL_card : Nat.card (PSL(2,GoldenFour))=60 := by
  rw [← Nat.card_congr goldenFourSLPSL.toEquiv,goldenFour_SL_card]

abbrev GoldenFourProjectiveLine := ℙ GoldenFour (Fin 2 → GoldenFour)

instance goldenFourProjectiveLine_fintype : Fintype GoldenFourProjectiveLine := Fintype.ofFinite _

theorem goldenFourProjectiveLine_card : Nat.card GoldenFourProjectiveLine=5 := by
  rw [Atlas.card_projectiveSpace]
  have hc : Nat.card GoldenFour=4 := by rw [Nat.card_eq_fintype_card,goldenFour_card]
  rw [hc]
  norm_num

/-- A coordinate marking of the actual five-point projective line. -/
def goldenFourProjectiveMarking : GoldenFourProjectiveLine ≃ Fin 5 :=
  Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using goldenFourProjectiveLine_card)

def goldenFourPSLToFivePerm : PSL(2,GoldenFour) →* Equiv.Perm (Fin 5) :=
  goldenFourProjectiveMarking.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (PSL(2,GoldenFour)) GoldenFourProjectiveLine)

theorem goldenFourPSLToFivePerm_injective : Function.Injective goldenFourPSLToFivePerm := by
  intro g h he
  apply (MulAction.toPerm_injective (β := GoldenFourProjectiveLine))
  exact goldenFourProjectiveMarking.permCongrHom.injective he

/-- The natural faithful action is even, by the retained uniform PSL simplicity theorem. -/
theorem goldenFourPSLToFivePerm_sign (g : PSL(2,GoldenFour)) :
    Equiv.Perm.sign (goldenFourPSLToFivePerm g)=1 := by
  have hc : Nat.card GoldenFour=4 := by rw [Nat.card_eq_fintype_card,goldenFour_card]
  letI : IsSimpleGroup (PSL(2,GoldenFour)) := Atlas.psl_simple_rank_two (by rw [hc])
  let s := Equiv.Perm.sign.comp goldenFourPSLToFivePerm
  have hs : s.ker=⊤ := by
    rcases s.normal_ker.eq_bot_or_eq_top with h | h
    · have hi := s.ker_eq_bot_iff.mp h
      have hh := Nat.card_le_card_of_injective s hi
      have hz : Nat.card ℤˣ=2 := by simp [Nat.card_eq_fintype_card]
      rw [goldenFour_PSL_card,hz] at hh
      omega
    · exact h
  have hg : g ∈ s.ker := hs ▸ Subgroup.mem_top g
  exact (MonoidHom.mem_ker.mp hg : s g = 1)

def goldenFourPSLToAlternating : PSL(2,GoldenFour) →* alternatingGroup (Fin 5) :=
  goldenFourPSLToFivePerm.codRestrict _ goldenFourPSLToFivePerm_sign

theorem goldenFourPSLToAlternating_bijective : Function.Bijective goldenFourPSLToAlternating := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro g h he
    exact goldenFourPSLToFivePerm_injective (congrArg Subtype.val he)
  · rw [goldenFour_PSL_card,nat_card_alternatingGroup]
    norm_num

/-- Identification with the actual alternating group through the explicit
five-point projective action, not recognition from an abstract order. -/
def goldenFourSLAlternatingFive : SL(2,GoldenFour) ≃* alternatingGroup (Fin 5) :=
  goldenFourSLPSL.trans (MulEquiv.ofBijective goldenFourPSLToAlternating
    goldenFourPSLToAlternating_bijective)

end Atlas.Algebra
