import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionCenterQuotient
import Atlas.LinearGroups.Chevalley.Integral.E6Minuscule.Quotient
import Mathlib.GroupTheory.OrderOfElement

/-! Exponent three for the actual adjoint kernel, deduced from the verified
integral weight/root quotient. No finite E6 group-order formula is used. -/
noncomputable section
namespace Atlas.Chevalley.TwistedE6
open Integral.Minuscule
variable (K : Type*) [Field K] [Finite K]

theorem companion_rhoKernel_cube (g : SelectedWeightCompanion .E6 K)
    (hg : g ∈ (selectedWeightCompanionRho .E6 K).ker) : g ^ 3 = 1 := by
  have hz : g ∈ Subgroup.center (SelectedWeightCompanion .E6 K) := by
    rw [selectedWeightCompanion_center_eq_rhoKernel]
    exact hg
  let z : Subgroup.center (SelectedWeightCompanion .E6 K) := ⟨g, hz⟩
  let e := selectedWeightCompanionCenterCharacterEquiv .E6 K
  have hc : Nat.card (Multiplicative (E6Minuscule.Weight ⧸ rootLattice E6Data.pairing)) = 3 :=
    (Nat.card_congr Multiplicative.toAdd).trans E6Minuscule.weightRootQuotient_card
  have hthree : z ^ 3 = 1 := by
    apply e.injective
    apply MonoidHom.ext
    intro w
    have hw : w ^ 3 = 1 := by
      rw [← hc]
      exact pow_card_eq_one'
    simpa only [map_pow, MonoidHom.pow_apply, map_one, MonoidHom.one_apply] using
      congrArg (e z) hw
  exact congrArg Subtype.val hthree

end Atlas.Chevalley.TwistedE6
