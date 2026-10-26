import Atlas.LinearGroups.F4.OppositePointOrbit

/-! The intrinsic opposition relation, its invariance, and the full opposite
orbit of every point stabilizer. No numerical F₄ order is used. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F]

/-- Two white trace-zero points are opposite when their trace pairing is nonzero. -/
def PointsOpposite (x y : WhiteZeroPoints F) : Prop :=
  tracePairing x.val.rep y.val.rep ≠ 0

theorem pointsOpposite_symm {x y : WhiteZeroPoints F} :
    PointsOpposite x y ↔ PointsOpposite y x := by
  unfold PointsOpposite
  rw [tracePairing_comm]

theorem action_rep_scale (g : Model F) (x : WhiteZeroPoints F) :
    ∃ s : Fˣ, (g • x).val.rep = s.val • g.val x.val.rep := by
  have hn : g.val x.val.rep ≠ 0 := fun h => Projectivization.rep_nonzero x.val
    (g.val.injective (h.trans (g.val.map_zero).symm))
  obtain ⟨s,hs⟩ := Projectivization.exists_smul_eq_mk_rep F (g.val x.val.rep) hn
  refine ⟨s, ?_⟩
  change (g.val • x.val).rep = _
  conv_lhs => rw [← Projectivization.mk_rep x.val, Projectivization.smul_mk]
  exact hs.symm

theorem pointsOpposite_smul_iff (g : Model F) (x y : WhiteZeroPoints F) :
    PointsOpposite (g • x) (g • y) ↔ PointsOpposite x y := by
  obtain ⟨s,hs⟩ := action_rep_scale g x
  obtain ⟨t,ht⟩ := action_rep_scale g y
  unfold PointsOpposite
  rw [hs,ht,tracePairing_smul_left,tracePairing_comm (g.val x.val.rep),
    tracePairing_smul_left,tracePairing_comm,stabilizer_tracePairing]
  simp only [mul_ne_zero_iff]
  have hs0 : (s : F) ≠ 0 := s.ne_zero
  have ht0 : (t : F) ≠ 0 := t.ne_zero
  tauto

theorem pointsOpposite_parabolic_iff (x : WhiteZeroPoints F) :
    PointsOpposite parabolicPoint x ↔ tracePairing parabolicVector x.val.rep ≠ 0 := by
  obtain ⟨s,hs⟩ := Projectivization.exists_smul_eq_mk_rep F
    (parabolicVector (F:=F)) parabolicVector_ne_zero
  change tracePairing (Projectivization.mk F parabolicVector _).rep x.val.rep ≠ 0 ↔ _
  rw [←hs]
  change tracePairing (s.val • parabolicVector) x.val.rep ≠ 0 ↔ _
  rw [tracePairing_smul_left]
  simp only [mul_ne_zero_iff]
  have hs0 : (s : F) ≠ 0 := s.ne_zero
  tauto

/-- The actual stabilizer of each point is transitive on its opposite points. -/
theorem opposite_points_stabilizer_transitive (x y z : WhiteZeroPoints F)
    (hy : PointsOpposite x y) (hz : PointsOpposite x z) :
    ∃ g : MulAction.stabilizer (Model F) x, g • y = z := by
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq (Model F) x parabolicPoint
  have hy' : PointsOpposite parabolicPoint (a • y) := by
    rw [←ha,pointsOpposite_smul_iff]
    exact hy
  have hz' : PointsOpposite parabolicPoint (a • z) := by
    rw [←ha,pointsOpposite_smul_iff]
    exact hz
  obtain ⟨b,hb⟩ := opposite_points_parabolic_transitive_pairing (a • y) (a • z)
    ((pointsOpposite_parabolic_iff _).mp hy') ((pointsOpposite_parabolic_iff _).mp hz')
  have hm : a⁻¹*b.val*a ∈ MulAction.stabilizer (Model F) x := by
    change (a⁻¹*b.val*a) • x = x
    rw [mul_smul,mul_smul,ha]
    have hfix : b.val • parabolicPoint = parabolicPoint := b.prop
    rw [hfix,←ha,inv_smul_smul]
  refine ⟨⟨a⁻¹*b.val*a,hm⟩, ?_⟩
  change (a⁻¹*b.val*a) • y = z
  rw [mul_smul,mul_smul,hb,inv_smul_smul]

theorem pointsOpposite_common (x y : WhiteZeroPoints F) :
    ∃ z, PointsOpposite x z ∧ PointsOpposite y z :=
  whiteZeroPoints_common_opposite x y

end Atlas.F4
