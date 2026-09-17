import Atlas.Comparisons.Exceptional.Order20160A8
import Atlas.GroupTheory.SylowCenterInvariant
import Atlas.LinearGroups.UnitriangularThreeProjective
import Atlas.LinearGroups.UnitriangularFourProjective

/-! Equal-order nonisomorphism from centers of the actual Sylow-two subgroups. -/
noncomputable section
namespace Atlas.Comparisons.Exceptional
open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F]
local instance exceptional20160PrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem psl4Two_not_equiv_psl3Card4 (hF : Nat.card F = 4) :
    ¬ Nonempty (PSL(4,ZMod 2) ≃* PSL(3,F)) := by
  apply Atlas.GroupTheory.not_mulEquiv_of_sylow_center_card_ne
    (Atlas.LinearGroups.UnitriangularFour.sylowTwo (ZMod 2) (by simp))
    (Atlas.LinearGroups.UnitriangularThree.sylowTwo F hF)
  rw [Atlas.LinearGroups.UnitriangularFour.sylowTwo_center_card,
    Atlas.LinearGroups.UnitriangularThree.sylowTwo_center_card]
  decide

theorem alt8_not_equiv_psl3Card4 (hF : Nat.card F = 4) :
    ¬ Nonempty (alternatingGroup (Fin 8) ≃* PSL(3,F)) := by
  rintro ⟨e⟩
  exact psl4Two_not_equiv_psl3Card4 hF ⟨psl4TwoEquivAlt8.trans e⟩

theorem psl4Two_card_eq_psl3Card4 (hF : Nat.card F = 4) :
    Nat.card PSL(4,ZMod 2) = Nat.card PSL(3,F) := by
  rw [psl4Two_card,Atlas.LinearGroups.UnitriangularThree.psl3_card_four F hF]

theorem alt8_card_eq_psl3Card4 (hF : Nat.card F = 4) :
    Nat.card (alternatingGroup (Fin 8)) = Nat.card PSL(3,F) := by
  rw [alt8_card,Atlas.LinearGroups.UnitriangularThree.psl3_card_four F hF]

end Atlas.Comparisons.Exceptional
