import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2PerfectnessOdd

/-! Finite-field wrapper. The q>3 theorem is already proved for all
root data; only q=3 uses the new rank-two argument. Characteristic two with
q≥4 is therefore included without any characteristic restriction. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo
open Group ClassicalData
local instance c2FiniteRootDecidableEq : DecidableEq (BRoot 2) := Classical.decEq _
local instance c2FiniteBaseDecidableEq : DecidableEq (baseC 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseC 1).support})
variable (K : Type*) [Field K] [Fintype K]

/-- Perfectness holds for this actual C2 adjoint group over every finite field q>2. -/
theorem c2_adjoint_isPerfect_of_card_gt_two (hq : 2 < Fintype.card K) :
    IsPerfect (Adjoint (pairingC 2) (baseC 1) K) := by
  by_cases hlarge : 3 < Fintype.card K
  · exact adjoint_isPerfect_of_card_gt_three (pairingC 2) (baseC 1) K hlarge
  · exact c2_adjoint_isPerfect_of_card_three K (by omega)

end Atlas.Chevalley.Integral.RankTwo

namespace Atlas.Chevalley
open Group
local instance c2ModelRootDecidableEq : DecidableEq (ClassicalData.BRoot 2) :=
  Classical.decEq _
local instance c2ModelBaseDecidableEq : DecidableEq (ClassicalData.baseC 1).support :=
  inferInstanceAs (DecidableEq {i : ClassicalData.BRoot 2 // i ∈ (ClassicalData.baseC 1).support})
variable (K : Type*) [Field K]

/-- The dispatcher C2 branch uses exactly pairingC 2 and baseC 1. -/
theorem model_C2_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (Model (.C 2 (by decide)) K) := by
  change IsPerfect (Adjoint (ClassicalData.pairingC 2) (ClassicalData.baseC 1) K)
  exact Integral.RankTwo.c2_adjoint_isPerfect_of_neg_one_ne_one K hchar

/-- Public-model form of the all-finite-fields C2 result; q=2 is excluded. -/
theorem model_C2_isPerfect_of_card_gt_two [Fintype K]
    (hq : 2 < Fintype.card K) : IsPerfect (Model (.C 2 (by decide)) K) := by
  change IsPerfect (Adjoint (ClassicalData.pairingC 2) (ClassicalData.baseC 1) K)
  exact Integral.RankTwo.c2_adjoint_isPerfect_of_card_gt_two K hq

end Atlas.Chevalley
