import Atlas.LinearGroups.Chevalley.RootData.E8RootParabolicRepresentatives
import Atlas.LinearGroups.Chevalley.RootData.E8E7Parabolic

/-! The actual E8/E7 Weyl length factor, using the240 literal shortest root
paths and the proved length-preserving parabolic equivalence. -/
noncomputable section
namespace Atlas.Chevalley.E8E7
open Classical RootData
open scoped BigOperators
local instance : Fintype E7Data.pairing.weylGroupToPerm.range := Fintype.ofFinite _
local instance : Fintype
    (rootParabolicSubgroup E8Data.pairing E8Data.base E8Parabolic.J) := Fintype.ofFinite _

theorem rootWeylPoincareEval_E8_E7 (q : ℕ) :
    rootWeylPoincareEval E8Data.pairing E8Data.base q =
      ((∑ k : Fin 30, q ^ k.val) *
        (1 + q ^ 6 + q ^ 12 + q ^ 18) * (1 + q ^ 10)) *
        rootWeylPoincareEval E7Data.pairing E7Data.base q := by
  rw [E8RootOrbit.rootWeylPoincareEval_E8_parabolic]
  have hs : (∑ v : rootParabolicSubgroup E8Data.pairing E8Data.base E8Parabolic.J,
      q ^ rootWeylLength E8Data.pairing E8Data.base v.val) =
        rootWeylPoincareEval E7Data.pairing E7Data.base q := by
    rw [← parabolicEquiv.toEquiv.sum_comp
      (fun v => q ^ rootWeylLength E8Data.pairing E8Data.base v.val)]
    change (∑ w : E7Data.pairing.weylGroupToPerm.range,
      q ^ rootWeylLength E8Data.pairing E8Data.base (parabolicEquiv.toEquiv w).val) =
        ∑ w : E7Data.pairing.weylGroupToPerm.range,
          q ^ rootWeylLength E7Data.pairing E7Data.base w
    apply Finset.sum_congr rfl
    intro w hw
    change q ^ rootWeylLength E8Data.pairing E8Data.base (parabolicEquiv w).val = _
    exact congrArg (fun n : ℕ => q ^ n) (parabolicEquiv_length w)
  rw [hs]

end Atlas.Chevalley.E8E7
