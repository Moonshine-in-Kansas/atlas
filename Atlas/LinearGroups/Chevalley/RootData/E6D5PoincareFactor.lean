import Atlas.LinearGroups.Chevalley.RootData.E6WeightParabolicRepresentatives
import Atlas.LinearGroups.Chevalley.RootData.E6D5Parabolic

/-! Actual E6/D5 Poincaré factorization. The27-point quotient polynomial
and the literal length-preserving D5 parabolic equivalence are both proved
in the prerequisites; no Weyl order or group recognition is assumed. -/
noncomputable section
namespace Atlas.Chevalley.E6D5
open Classical RootData
open scoped BigOperators
local instance : Fintype E6Data.Root := Fintype.ofFinite _
local instance : Fintype (ClassicalData.pairingD 5).weylGroupToPerm.range :=
  Fintype.ofFinite _
local instance : Fintype
    (rootParabolicSubgroup E6Data.pairing E6Data.base E6Parabolic.J) := Fintype.ofFinite _

theorem rootWeylPoincareEval_E6_D5 (q : ℕ) :
    rootWeylPoincareEval E6Data.pairing E6Data.base q =
      ((∑ k : Fin 9, q ^ k.val) * (1 + q ^ 4 + q ^ 8)) *
        rootWeylPoincareEval (ClassicalData.pairingD 5) (ClassicalData.baseD 3) q := by
  rw [E6WeightOrbit.rootWeylPoincareEval_E6_parabolic]
  have hs : (∑ v : rootParabolicSubgroup E6Data.pairing E6Data.base E6Parabolic.J,
      q ^ rootWeylLength E6Data.pairing E6Data.base v.val) =
        rootWeylPoincareEval (ClassicalData.pairingD 5) (ClassicalData.baseD 3) q := by
    rw [← parabolicEquiv.toEquiv.sum_comp
      (fun v => q ^ rootWeylLength E6Data.pairing E6Data.base v.val)]
    change (∑ w : (ClassicalData.pairingD 5).weylGroupToPerm.range,
      q ^ rootWeylLength E6Data.pairing E6Data.base (parabolicEquiv.toEquiv w).val) =
        ∑ w : (ClassicalData.pairingD 5).weylGroupToPerm.range,
          q ^ rootWeylLength (ClassicalData.pairingD 5) (ClassicalData.baseD 3) w
    apply Finset.sum_congr rfl
    intro w hw
    change q ^ rootWeylLength E6Data.pairing E6Data.base (parabolicEquiv w).val = _
    exact congrArg (fun n : ℕ => q ^ n) (parabolicEquiv_length w)
  rw [hs]

end Atlas.Chevalley.E6D5
