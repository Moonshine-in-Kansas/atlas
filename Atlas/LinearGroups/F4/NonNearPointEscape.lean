import Atlas.LinearGroups.F4.PointOpposition
import Atlas.LinearGroups.F4.ParabolicPairingEscape
import Atlas.GroupTheory.PrimitivePointChains

/-! Two genuine stabilizer moves suffice for every white point outside the
near nine-space. No parabolic orbit classification or order is assumed. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert Atlas.GroupTheory
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F]

theorem nonnear_point_parabolic_move (x : WhiteZeroPoints F)
    (hx : x.val.rep ∉ parabolicImageZero (F:=F)) :
    ∃ g : parabolicPointStabilizer (F:=F), PointsOpposite x (g.val • x) := by
  obtain ⟨g,hg⟩ := nonnear_parabolic_self_pairing x.val.rep x.prop.2 x.prop.1 hx
  refine ⟨g,?_⟩
  obtain ⟨s,hs⟩ := action_rep_scale g.val x
  unfold PointsOpposite
  rw [hs,tracePairing_comm,tracePairing_smul_left,tracePairing_comm]
  exact mul_ne_zero s.ne_zero hg

/-- A root move fixing C₀ produces a point opposite to `x`; a move fixing `x`
then sends it to a common opposite of `x` and C₀. -/
theorem nonnear_point_stabilizer_chain_escape (x : WhiteZeroPoints F)
    (hx : x.val.rep ∉ parabolicImageZero (F:=F)) :
    ∃z : WhiteZeroPoints F,
      StabilizerMoveChain (Model F) (parabolicPoint (F:=F)) x z ∧
      PointsOpposite (parabolicPoint (F:=F)) z := by
  obtain ⟨g,hg⟩ := nonnear_point_parabolic_move x hx
  obtain ⟨z,hpz,hxz⟩ := pointsOpposite_common (parabolicPoint (F:=F)) x
  obtain ⟨h,hh⟩ := opposite_points_stabilizer_transitive x (g.val • x) z hg hxz
  have hy : StabilizerMoveChain (Model F) (parabolicPoint (F:=F)) x (g.val • x) :=
    .move (parabolicPoint (F:=F)) x .left .right g
  refine ⟨z,?_,hpz⟩
  rw [←hh]
  exact .move x (g.val • x) .right hy h

end Atlas.F4
