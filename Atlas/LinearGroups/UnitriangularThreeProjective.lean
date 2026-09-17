import Atlas.LinearGroups.UpperUnitriangularThree
import Atlas.LinearGroups.PSLFamily
import Mathlib.GroupTheory.Sylow

noncomputable section
namespace Atlas.LinearGroups.UnitriangularThree
open Matrix
open scoped MatrixGroups
variable (F : Type*) [Field F]

def projective : subgroup F →* PSL(3,F) :=
  (QuotientGroup.mk' (Subgroup.center SL(3,F))).comp (subgroup F).subtype

theorem projective_injective : Function.Injective (projective F) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro g hg
  have hc : g.val ∈ Subgroup.center SL(3,F) :=
    (QuotientGroup.eq_one_iff _).mp hg
  obtain ⟨r,hr,he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  obtain ⟨v,hv⟩ := member_surjective F g
  subst g
  have hd := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) he
  have hr1 : r = 1 := by simpa [member,element,mat,Matrix.scalar_apply] using hd
  change member F v = 1
  apply Subtype.ext
  apply Subtype.ext
  simpa [hr1] using he.symm

variable [Finite F]
theorem psl3_card_four (hF : Nat.card F = 4) : Nat.card PSL(3,F) = 20160 := by
  rw [Atlas.card_psl_factor (F := F) 3,hF]
  norm_num [Finset.prod_Icc_succ_top]

theorem projective_range_card : Nat.card (projective F).range = Nat.card F ^ 3 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (projective_injective F)).toEquiv,card]

local instance unitriangularThreePrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

def sylowTwo (hF : Nat.card F = 4) : Sylow 2 PSL(3,F) :=
  Sylow.ofCard (projective F).range (by
    rw [projective_range_card,hF,psl3_card_four F hF]
    decide +kernel)

def sylowModelEquiv (hF : Nat.card F = 4) : subgroup F ≃* sylowTwo F hF :=
  MonoidHom.ofInjective (projective_injective F)

theorem sylowTwo_card (hF : Nat.card F = 4) : Nat.card (sylowTwo F hF) = 64 := by
  rw [← Nat.card_congr (sylowModelEquiv F hF).toEquiv,card,hF]
  norm_num

theorem sylowTwo_center_card (hF : Nat.card F = 4) :
    Nat.card (Subgroup.center (sylowTwo F hF)) = 4 := by
  rw [← Nat.card_congr (Subgroup.centerCongr (sylowModelEquiv F hF)).toEquiv,center_card,hF]

end Atlas.LinearGroups.UnitriangularThree
