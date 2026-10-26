import Atlas.LinearGroups.Chevalley.C2BinarySign
import Atlas.LinearGroups.Chevalley.ModelBCOrder
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.B2C2AdjointEquiv

/-! The actual binary B2/C2 exceptions. The six-form sign character has
proper nontrivial kernel. The adjoint projection is an actual bijective
homomorphism here, using its independently verified source and target orders.
No earlier symplectic or orthogonal group theorem is imported. -/
noncomputable section
namespace Atlas.Chevalley.C2Binary
open Classical Integral.RankTwo.C2Minuscule
local instance : NeZero C2.rank := ⟨by decide⟩

theorem companion_card : Nat.card G = 720 := by
  rw [selectedWeightCompanion_C_card]
  norm_num [Nat.card_zmod, Finset.prod_range_succ]

theorem adjoint_card : Nat.card (Model C2 K) = 720 := by
  rw [model_C_card]
  norm_num [Nat.card_zmod, Finset.prod_range_succ]

def projectionEquiv : G ≃* Model C2 K :=
  MulEquiv.ofBijective (selectedWeightCompanionRho C2 K)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨selectedWeightCompanionRho_surjective C2 K, companion_card.trans adjoint_card.symm⟩)

theorem companion_not_simple : ¬ IsSimpleGroup G := by
  intro hs
  letI := hs
  rcases (inferInstance : oddSign.ker.Normal).eq_bot_or_eq_top with hk | hk
  · have hi := (MonoidHom.ker_eq_bot_iff oddSign).mp hk
    have hc := Nat.card_le_card_of_injective oddSign hi
    rw [companion_card] at hc
    norm_num [Nat.card_eq_fintype_card] at hc
  · have hm : selectedWeightCompanionX C2 K 1 1 ∈ oddSign.ker :=
      hk ▸ Subgroup.mem_top _
    have he : oddSign (selectedWeightCompanionX C2 K 1 1) = 1 := hm
    rw [oddSign_long_root] at he
    exact (by decide : (-1 : ℤˣ) ≠ 1) he

theorem model_C2_binary_not_simple : ¬ IsSimpleGroup (Model C2 K) := by
  intro hs
  letI := hs
  exact companion_not_simple projectionEquiv.isSimpleGroup

end Atlas.Chevalley.C2Binary

namespace Atlas.Chevalley

theorem model_C_two_two_not_simple (F : Type*) [Field F] [Finite F]
    (hq : Nat.card F = 2) : ¬ IsSimpleGroup (Model (.C 2 (by decide)) F) := by
  letI : Fintype F := Fintype.ofFinite F
  let e : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hq)
  intro hs
  letI := hs
  exact C2Binary.model_C2_binary_not_simple
    (modelEquiv Integral.RankTwo.C2Minuscule.C2 e).isSimpleGroup

theorem model_B_two_two_not_simple (F : Type*) [Field F] [Finite F]
    (hq : Nat.card F = 2) : ¬ IsSimpleGroup (Model (.B 2 (by decide)) F) := by
  classical
  intro hs
  letI : IsSimpleGroup (Adjoint (ClassicalData.pairingB 2) (ClassicalData.baseB 1) F) := hs
  exact model_C_two_two_not_simple F hq
    (Integral.RankTwo.b2c2AdjointEquiv F).symm.isSimpleGroup

end Atlas.Chevalley
