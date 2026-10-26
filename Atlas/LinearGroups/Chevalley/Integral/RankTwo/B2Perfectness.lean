import Atlas.LinearGroups.Chevalley.Integral.RankTwo.B2C2AdjointEquiv
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2PerfectnessFinite

/-! UNCHECKED final B2 continuation. Perfectness is transferred along the
actual all-characteristic ten-coordinate B2/C2 group isomorphism. No legacy
orthogonal/symplectic order or simplicity theorem is used. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo
open Group ClassicalData
local instance b2PerfectRootDecidableEq : DecidableEq (BRoot 2) := Classical.decEq _
local instance b2PerfectBaseDecidableEq : DecidableEq (baseB 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseB 1).support})
local instance c2PerfectTransportBaseDecidableEq : DecidableEq (baseC 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseC 1).support})
variable (K : Type*) [Field K]

/-- The actual B2 group is perfect in characteristic different from two. -/
theorem b2_adjoint_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (Adjoint (pairingB 2) (baseB 1) K) := by
  letI : IsPerfect (Adjoint (pairingC 2) (baseC 1) K) :=
    c2_adjoint_isPerfect_of_neg_one_ne_one K hchar
  exact Group.IsPerfect.ofSurjective (f := (b2c2AdjointEquiv K).symm.toMonoidHom)
    (b2c2AdjointEquiv K).symm.surjective

/-- All finite q>2, including characteristic two when q≥4. -/
theorem b2_adjoint_isPerfect_of_card_gt_two [Fintype K]
    (hq : 2 < Fintype.card K) : IsPerfect (Adjoint (pairingB 2) (baseB 1) K) := by
  letI : IsPerfect (Adjoint (pairingC 2) (baseC 1) K) :=
    c2_adjoint_isPerfect_of_card_gt_two K hq
  exact Group.IsPerfect.ofSurjective (f := (b2c2AdjointEquiv K).symm.toMonoidHom)
    (b2c2AdjointEquiv K).symm.surjective

end Atlas.Chevalley.Integral.RankTwo

namespace Atlas.Chevalley
open Group
local instance b2ModelRootDecidableEq : DecidableEq (ClassicalData.BRoot 2) :=
  Classical.decEq _
local instance b2ModelBaseDecidableEq : DecidableEq (ClassicalData.baseB 1).support :=
  inferInstanceAs (DecidableEq {i : ClassicalData.BRoot 2 // i ∈ (ClassicalData.baseB 1).support})
variable (K : Type*) [Field K]

/-- The B2 dispatcher uses exactly the transported actual B2 root datum. -/
theorem model_B2_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (Model (.B 2 (by decide)) K) := by
  change IsPerfect (Adjoint (ClassicalData.pairingB 2) (ClassicalData.baseB 1) K)
  exact Integral.RankTwo.b2_adjoint_isPerfect_of_neg_one_ne_one K hchar

/-- Public-model form of the actual finite-field B2 perfectness theorem. -/
theorem model_B2_isPerfect_of_card_gt_two [Fintype K]
    (hq : 2 < Fintype.card K) : IsPerfect (Model (.B 2 (by decide)) K) := by
  change IsPerfect (Adjoint (ClassicalData.pairingB 2) (ClassicalData.baseB 1) K)
  exact Integral.RankTwo.b2_adjoint_isPerfect_of_card_gt_two K hq

end Atlas.Chevalley
