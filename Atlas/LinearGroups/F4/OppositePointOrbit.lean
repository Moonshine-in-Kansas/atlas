import Atlas.LinearGroups.F4.PointTransitivity
import Atlas.LinearGroups.F4.OppositeCellParabolicAction
import Atlas.LinearGroups.F4.CommonOpposite
import Atlas.Algebra.Albert.TraceNormalization

/-! Opposite projective points form one actual parabolic orbit. These facts
use the normalized affine cell, not a group-order or simplicity argument. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F]

def normalizeOppositeVector (x : Carrier F) (ha : adjoint x=0)
    (ht : trace x=0) (hc : x.2 2 7≠0) : OppositeCell F :=
  ⟨(x.2 2 7)⁻¹ • x,by
    refine ⟨?_,?_,?_⟩
    · rw [adjoint_smul,ha,smul_zero]
    · rw [trace_smul,ht,mul_zero]
    · exact inv_mul_cancel₀ hc⟩

theorem opposite_vectors_parabolic_transport (x y : Carrier F)
    (ha : adjoint x=0) (ht : trace x=0) (hc : x.2 2 7≠0)
    (hb : adjoint y=0) (hu : trace y=0) (hd : y.2 2 7≠0) :
    ∃ (g : parabolicPointStabilizer (F:=F)) (s : Fˣ), g.val.val x=s.val • y := by
  obtain ⟨g,hg⟩ := oppositeCell_transitive
    (normalizeOppositeVector x ha ht hc) (normalizeOppositeVector y hb hu hd)
  change g.val.val ((x.2 2 7)⁻¹ • x)=(y.2 2 7)⁻¹ • y at hg
  rw [_root_.map_smul] at hg
  have he := congrArg (fun z : Carrier F => x.2 2 7 • z) hg
  rw [smul_smul,mul_inv_cancel₀ hc,one_smul,smul_smul] at he
  exact ⟨g,Units.mk0 (x.2 2 7*(y.2 2 7)⁻¹) (mul_ne_zero hc (inv_ne_zero hd)),he⟩

theorem opposite_points_parabolic_transitive (x y : WhiteZeroPoints F)
    (hx : x.val.rep.2 2 7≠0) (hy : y.val.rep.2 2 7≠0) :
    ∃ g : parabolicPointStabilizer (F:=F), g.val • x=y := by
  obtain ⟨g,s,hs⟩ := opposite_vectors_parabolic_transport x.val.rep y.val.rep
    x.prop.2 x.prop.1 hx y.prop.2 y.prop.1 hy
  refine ⟨g,Subtype.ext ?_⟩
  change g.val.val • x.val=y.val
  rw [←Projectivization.mk_rep x.val,←Projectivization.mk_rep y.val,
    Projectivization.smul_mk,Projectivization.mk_eq_mk_iff]
  exact ⟨s,hs.symm⟩

theorem opposite_points_parabolic_transitive_pairing (x y : WhiteZeroPoints F)
    (hx : tracePairing parabolicVector x.val.rep≠0)
    (hy : tracePairing parabolicVector y.val.rep≠0) :
    ∃ g : parabolicPointStabilizer (F:=F), g.val • x=y := by
  rw [parabolicPairing_C7] at hx hy
  exact opposite_points_parabolic_transitive x y hx hy

/-- Every two nonzero white trace-zero vectors have a common opposite vector. -/
theorem whiteZero_vectors_common_opposite (x y : Carrier F)
    (hx : x≠0) (ha : adjoint x=0) (ht : trace x=0)
    (hy : y≠0) (hb : adjoint y=0) (hu : trace y=0) :
    ∃ z : Carrier F, z≠0 ∧ adjoint z=0 ∧ trace z=0 ∧
      tracePairing x z≠0 ∧ tracePairing y z≠0 := by
  obtain ⟨g,hg⟩ := whiteZero_vectors_transitive x parabolicVector hx ha ht
    parabolicVector_ne_zero parabolicVector_adjoint parabolicVector_trace
  obtain ⟨z,hz⟩ := whiteZero_common_opposite (g.val y)
    (fun h => hy (g.val.injective (h.trans (g.val.map_zero).symm)))
    (by rw [stabilizer_adjoint,hb,map_zero])
    (by rw [stabilizer_trace,hu])
  have hz0 : z.val≠0 := by
    intro h
    have he := z.prop.2.2
    rw [h] at he
    exact zero_ne_one he
  refine ⟨g.val.symm z.val,?_,?_,?_,?_,?_⟩
  · exact fun h => hz0 (g.val.symm.injective (h.trans (g.val.symm.map_zero).symm))
  · change adjoint ((g⁻¹).val z.val)=0
    rw [stabilizer_adjoint,z.prop.1,map_zero]
  · change trace ((g⁻¹).val z.val)=0
    rw [stabilizer_trace,z.prop.2.1]
  · have he := stabilizer_tracePairing g x (g.val.symm z.val)
    rw [hg,g.val.apply_symm_apply,parabolicPairing_C7,z.prop.2.2] at he
    rw [←he]
    exact one_ne_zero
  · have he := stabilizer_tracePairing g y (g.val.symm z.val)
    rw [g.val.apply_symm_apply] at he
    rwa [←he]

/-- Common opposites for the actual projective white-point action. -/
theorem whiteZeroPoints_common_opposite (x y : WhiteZeroPoints F) :
    ∃ z : WhiteZeroPoints F, tracePairing x.val.rep z.val.rep≠0 ∧
      tracePairing y.val.rep z.val.rep≠0 := by
  obtain ⟨z,hz0,hza,hzt,hxz,hyz⟩ := whiteZero_vectors_common_opposite
    x.val.rep y.val.rep (Projectivization.rep_nonzero _) x.prop.2 x.prop.1
    (Projectivization.rep_nonzero _) y.prop.2 y.prop.1
  let p := whiteZeroPointMk F z hz0 hzt hza
  have hp : p.val=Projectivization.mk F z hz0 := rfl
  obtain ⟨s,hs⟩ := Projectivization.exists_smul_eq_mk_rep F z hz0
  refine ⟨p,?_,?_⟩
  · rw [hp,←hs,tracePairing_comm]
    change tracePairing (s.val • z) x.val.rep≠0
    rw [tracePairing_smul_left,tracePairing_comm]
    exact mul_ne_zero s.ne_zero hxz
  · rw [hp,←hs,tracePairing_comm]
    change tracePairing (s.val • z) y.val.rep≠0
    rw [tracePairing_smul_left,tracePairing_comm]
    exact mul_ne_zero s.ne_zero hyz

end Atlas.F4
