import Atlas.Algebra.IcosianReductionConjugation
import Atlas.Algebra.IcosianNormOneReduction
import Atlas.Algebra.IcosianDivision
import Atlas.Algebra.IcosianModuloTwoKernel
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Matrix Quaternion QuadraticAlgebra

/-- The column image of an actual icosian's matrix reduction. -/
def icosianReductionImage (x : icosianOrder) : Submodule GoldenFour (Fin 2 → GoldenFour) :=
  (Matrix.mulVecLin (icosianModuloTwo x)).range

theorem icosianNorm_two : icosianNorm (2 : IcosianQuaternion)=4 := by
  rw [icosianNorm_coordinates]
  simp [QuaternionAlgebra.re_ofNat,QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat,QuaternionAlgebra.imK_ofNat]
  norm_num

theorem icosianGoldenModuloTwo_two : goldenModuloTwo (2 : GoldenInteger)=0 := by
  ext <;> norm_num [goldenModuloTwo] <;> decide

theorem icosianReduction_norm_two_det {r : icosianOrder} (hr : icosianNorm r.val=2) :
    Matrix.det (icosianModuloTwo r)=0 := by
  rw [icosianModuloTwo_det]
  have h : icosianIntegralNorm r=2 := by
    apply goldenIntegerToRational_injective
    rw [icosianIntegralNorm_spec,hr,map_ofNat]
  rw [h,icosianGoldenModuloTwo_two]

/-- Image containment in the singular column space forces the adjugate product to vanish. -/
theorem icosianReduction_adjugate_mul_zero {r s : icosianOrder}
    (hr : icosianNorm r.val=2) (himage : icosianReductionImage s ≤ icosianReductionImage r) :
    Matrix.adjugate (icosianModuloTwo r)*icosianModuloTwo s=0 := by
  funext i j
  have hs : (fun k => icosianModuloTwo s k j) ∈ icosianReductionImage s := by
    refine ⟨Pi.single j 1,?_⟩
    change icosianModuloTwo s *ᵥ Pi.single j 1=(fun k => icosianModuloTwo s k j)
    exact Matrix.mulVec_single_one _ j
  obtain ⟨v,hv⟩ := himage hs
  change icosianModuloTwo r *ᵥ v=(fun k => icosianModuloTwo s k j) at hv
  change (Matrix.adjugate (icosianModuloTwo r) *ᵥ (fun k => icosianModuloTwo s k j)) i=0
  rw [← hv,Matrix.mulVec_mulVec,Matrix.adjugate_mul,icosianReduction_norm_two_det hr]
  simp

/-- Two norm-two icosians with the same reduction line differ by an actual norm-one right scalar. -/
theorem icosianNormTwo_associate_of_adjugate {r s : icosianOrder}
    (hr : icosianNorm r.val=2) (hs : icosianNorm s.val=2)
    (hzero : Matrix.adjugate (icosianModuloTwo r) * icosianModuloTwo s = 0) :
    ∃ u : icosianNormOneGroup,s.val=r.val*u.val.val := by
  have hz : icosianModuloTwo (icosianOrderStar r*s)=0 := by
    rw [map_mul,icosianModuloTwo_star]
    exact hzero
  obtain ⟨u,hu⟩ := (icosianModuloTwo_eq_zero_iff_two_mul _).mp hz
  have he : star r.val*s.val=2*u.val := congrArg Subtype.val hu
  have hn : icosianNorm u.val=1 := by
    have h := congrArg icosianNorm he
    rw [icosianNorm_mul,icosianNorm_mul,icosianNorm_two,hs] at h
    have hstar : icosianNorm (star r.val)=2 := (Quaternion.normSq_star r.val).trans hr
    rw [hstar] at h
    apply (mul_left_cancel₀ (show (4 : GoldenRational)≠0 by norm_num))
    norm_num only at h ⊢
    exact h.symm
  refine ⟨icosianNormOneGroupOf u.val u.property hn,?_⟩
  change s.val=r.val*u.val
  have h := congrArg (fun z => r.val*z) he
  have hnorm : r.val*star r.val=(2 : IcosianQuaternion) := by
    rw [Quaternion.self_mul_star]
    change (icosianNorm r.val : IcosianQuaternion)=2
    rw [hr]
    rfl
  rw [← mul_assoc,hnorm] at h
  apply (mul_left_cancel₀ (show (2 : IcosianQuaternion)≠0 by
    intro hz
    have hh := congrArg (fun q : IcosianQuaternion => q.re.re) hz
    norm_num [QuaternionAlgebra.re_ofNat] at hh))
  calc
    2*s.val=r.val*(2*u.val) := h
    _=2*(r.val*u.val) := by noncomm_ring

theorem icosianNormTwo_right_associate {r s : icosianOrder}
    (hr : icosianNorm r.val=2) (hs : icosianNorm s.val=2)
    (himage : icosianReductionImage s ≤ icosianReductionImage r) :
    ∃ u : icosianNormOneGroup,s.val=r.val*u.val.val :=
  icosianNormTwo_associate_of_adjugate hr hs (icosianReduction_adjugate_mul_zero hr himage)

end Atlas.Algebra

