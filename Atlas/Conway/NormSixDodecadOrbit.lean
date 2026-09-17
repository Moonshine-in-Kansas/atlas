import Atlas.Conway.GolayDodecadRestriction
import Atlas.Conway.MinimalEvenOrbits
import Atlas.Mathieu.DodecadFlags

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem normSix_dodecad_parameterization (x : leech) (hx : x.val ∈ twoFourFamily 12 0) :
    ∃ T : Finset Omega, T.card = 12 ∧ supportWord T ∈ golay ∧
      ∃ s : T → Bit, (∑ i, s i) = 0 ∧ x.val = fun i => 2 * signedSupport T s i := by
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hx
  have hz := Finset.card_eq_zero.mp p.2.1.prop.2
  refine ⟨p.1.val,p.1.prop.2,p.1.prop.1,p.2.2.1.val,?_,?_⟩
  · simpa [p.2.1.prop.2] using p.2.2.1.prop
  · funext i
    have he := congrFun hp i
    change 2 * signedSupport p.1.val p.2.2.1.val i +
      4 * signedSupport p.2.1.val p.2.2.2 i = x.val i at he
    have hzero : signedSupport p.2.1.val p.2.2.2 i = 0 := by
      have hi : i ∉ p.2.1.val := by rw [hz]; simp
      simp [signedSupport,hi]
    simpa [hzero] using he.symm

theorem dodecad_support_sign_realization (T : Finset Omega) (hT : T.card = 12)
    (hC : supportWord T ∈ golay) (s : T → Bit) (hs : ∑ i, s i = 0) :
    ∃ c : golay, signChange c.val (constantSupportVector 2 T) =
      fun i => 2 * signedSupport T s i := by
  have hw : (∑ i ∈ T, codeZeroExtend T s i) = 0 := by
    rw [← Finset.sum_coe_sort]
    simpa only [codeZeroExtend_apply] using hs
  obtain ⟨c,hc⟩ := golay_dodecad_restriction T hT hC (codeZeroExtend T s) hw
  exact ⟨c,sign_constantSupport 2 T s c (fun i =>
    (hc i i.prop).trans (codeZeroExtend_apply T s i))⟩

theorem codeSupport_dodecad (T : Finset Omega) (hT : T.card = 12)
    (hC : supportWord T ∈ golay) : T ∈ dodecads := by
  apply (dodecads_mem T).mpr
  refine ⟨⟨supportWord T,hC⟩,?_,binarySupportEquiv.right_inv T⟩
  simpa [hammingNorm,supportWord] using hT

theorem monomial_dodecad_six_transitive (x y : leech)
    (hx : x.val ∈ twoFourFamily 12 0) (hy : y.val ∈ twoFourFamily 12 0) :
    ∃ m : GolayMonomialGroup, (monomialEmbedding m).val x = y := by
  obtain ⟨S,hS,hCS,s,hps,hs⟩ := normSix_dodecad_parameterization x hx
  obtain ⟨T,hT,hCT,t,hpt,ht⟩ := normSix_dodecad_parameterization y hy
  obtain ⟨c,hc⟩ := dodecad_support_sign_realization S hS hCS s hps
  obtain ⟨d,hd⟩ := dodecad_support_sign_realization T hT hCT t hpt
  obtain ⟨g,hg⟩ := dodecad_transitive_explicit
    ⟨S,codeSupport_dodecad S hS hCS⟩ ⟨T,codeSupport_dodecad T hT hCT⟩
  exact monomial_signed_support_transport g 2 S T hg c d x y (hs.trans hc.symm) (ht.trans hd.symm)

end Atlas.Conway
