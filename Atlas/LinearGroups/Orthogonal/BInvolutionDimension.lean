import Atlas.LinearGroups.Orthogonal.BAllRanksStructure
import Atlas.LinearGroups.Orthogonal.InvolutionKernelConjugacy
import Atlas.LinearAlgebra.InvolutionDeterminant
import Atlas.LinearAlgebra.QuadraticInvolutionTransport

/-! # The actual half-minus dimension of an odd-characteristic B involution -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.LinearInvolution
variable {F : Type*} [Field F] [Finite F]
variable (n : ℕ) (hn : 1 ≤ n) (h2 : (2 : F) ≠ 0)

include hn h2 in
theorem B_involution_data (g : elementarySubgroup (formB n F)) (ho : orderOf g = 2) :
    Function.Involutive g.val.val ∧ g.val.val.toLinearMap.det = 1 ∧
    spinorNorm (formB n F) (polarB_nondegenerate h2) h2 g.val = 1 ∧
    g.val.val.toLinearMap ≠ LinearMap.id := by
  have hp : g^2 = 1 := by simpa only [ho] using pow_orderOf_eq_one g
  have ht : Function.Involutive g.val.val := by
    intro x
    exact congrArg (fun a : elementarySubgroup (formB n F) => a.val.val x) hp
  have hg : g.val ∈ specialSubgroup (formB n F) ⊓
      (spinorNorm (formB n F) (polarB_nondegenerate h2) h2).ker := by
    rw [← B_odd_intrinsic_all_rank n hn h2]
    exact g.prop
  have hdet : g.val.val.det = 1 := hg.1
  have hdetP : g.val.val.toLinearMap.det = 1 := by
    simpa only [LinearEquiv.coe_det,Units.val_one] using congrArg Units.val hdet
  refine ⟨ht, hdetP, hg.2, ?_⟩
  intro he
  have hgone : g = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact LinearMap.congr_fun he x
  rw [hgone,orderOf_one] at ho
  omega

include hn h2 in
/-- Every genuine involution has one of the half-minus dimensions 1 through n. -/
theorem B_involution_half_minus_dimension
    (g : elementarySubgroup (formB n F)) (ho : orderOf g = 2) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ Module.finrank F (minus g.val.val.toLinearMap) = 2*m := by
  obtain ⟨ht,hdet,hspin,hne⟩ := B_involution_data n hn h2 g ho
  have hpos := two_le_finrank_minus_of_det_one g.val.val.toLinearMap ht h2 hdet hne
  obtain ⟨m,hm⟩ := even_finrank_minus_of_det_one g.val.val.toLinearMap ht h2 hdet
  have hbound := Submodule.finrank_le (minus g.val.val.toLinearMap)
  rw [vectorB_finrank] at hbound
  refine ⟨m, ?_, ?_, ?_⟩ <;> omega

include hn h2 in
/-- Equal half-minus dimensions give conjugacy in the actual elementary B group. -/
theorem B_involutions_isConj_of_minus_dimension
    (g h : elementarySubgroup (formB n F)) (ho : orderOf g = 2) (hp : orderOf h = 2)
    (hd : Module.finrank F (minus g.val.val.toLinearMap) =
      Module.finrank F (minus h.val.val.toLinearMap)) : IsConj g h := by
  obtain ⟨ht,hdet,hspin,hne⟩ := B_involution_data n hn h2 g ho
  obtain ⟨hs,hsdet,hsspin,hsne⟩ := B_involution_data n hn h2 h hp
  have hpos := two_le_finrank_minus_of_det_one g.val.val.toLinearMap ht h2 hdet hne
  obtain ⟨k,hk,hconj⟩ := involution_intrinsic_kernel_conjugator (formB n F)
    (polarB_nondegenerate h2) h2 g.val h.val ht hs hd hpos (hspin.trans hsspin.symm)
  have hke : k ∈ elementarySubgroup (formB n F) := by
    rwa [B_odd_intrinsic_all_rank n hn h2]
  exact isConj_iff.mpr ⟨⟨k,hke⟩,Subtype.ext hconj⟩
theorem B_involutions_minus_dimension_of_isConj
    (g h : elementarySubgroup (formB n F)) (hc : IsConj g h) :
    Module.finrank F (minus g.val.val.toLinearMap) =
      Module.finrank F (minus h.val.val.toLinearMap) := by
  obtain ⟨k,hk⟩ := isConj_iff.mp hc
  have he : Atlas.Quadratic.conjugateIsometry (formB n F) (formB n F)
      (isometryCarrierEquiv (formB n F) k.val) (isometryCarrierEquiv (formB n F) g.val) =
      isometryCarrierEquiv (formB n F) h.val := by
    apply DFunLike.coe_injective
    funext x
    exact congrArg (fun a : elementarySubgroup (formB n F) => a.val.val x) hk
  have hd := Atlas.Quadratic.conjugateIsometry_finrank_minus (formB n F) (formB n F)
    (isometryCarrierEquiv (formB n F) k.val) (isometryCarrierEquiv (formB n F) g.val)
  rw [he] at hd
  exact hd.symm

end Atlas.Orthogonal
