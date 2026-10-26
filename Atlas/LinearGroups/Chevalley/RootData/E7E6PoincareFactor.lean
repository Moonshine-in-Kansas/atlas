import Atlas.LinearGroups.Chevalley.RootData.E7WeightParabolicRepresentatives
import Atlas.LinearGroups.Chevalley.RootData.E7E6Parabolic

/-! Actual E7/E6 Poincare factorization. Both the56 shortest representatives
and the literal length-preserving E6 parabolic equivalence are proved inputs. -/
noncomputable section
namespace Atlas.Chevalley.E7E6
open Classical RootData
open scoped BigOperators
local instance : Fintype E6Data.Root := Fintype.ofFinite _
local instance : Fintype E6Data.pairing.weylGroupToPerm.range := Fintype.ofFinite _
local instance : Fintype
    (rootParabolicSubgroup E7Data.pairing E7Data.base E7WeightOrbit.J) := Fintype.ofFinite _

theorem rootWeylPoincareEval_E7_E6 (q : ℕ) :
    rootWeylPoincareEval E7Data.pairing E7Data.base q =
      ((∑ k : Fin 14, q ^ k.val) * (1 + q ^ 5) * (1 + q ^ 9)) *
        rootWeylPoincareEval E6Data.pairing E6Data.base q := by
  rw [E7WeightOrbit.rootWeylPoincareEval_E7_parabolic]
  have hs : (∑ v : rootParabolicSubgroup E7Data.pairing E7Data.base E7WeightOrbit.J,
      q ^ rootWeylLength E7Data.pairing E7Data.base v.val) =
        rootWeylPoincareEval E6Data.pairing E6Data.base q := by
    rw [← parabolicEquiv.toEquiv.sum_comp
      (fun v => q ^ rootWeylLength E7Data.pairing E7Data.base v.val)]
    change (∑ w : E6Data.pairing.weylGroupToPerm.range,
      q ^ rootWeylLength E7Data.pairing E7Data.base (parabolicEquiv.toEquiv w).val) =
        ∑ w : E6Data.pairing.weylGroupToPerm.range,
          q ^ rootWeylLength E6Data.pairing E6Data.base w
    apply Finset.sum_congr rfl
    intro w hw
    change q ^ rootWeylLength E7Data.pairing E7Data.base (parabolicEquiv w).val = _
    exact congrArg (fun n : ℕ => q ^ n) (parabolicEquiv_length w)
  rw [hs]

end Atlas.Chevalley.E7E6
