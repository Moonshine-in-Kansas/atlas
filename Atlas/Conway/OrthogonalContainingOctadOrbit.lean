import Atlas.Conway.MonomialMarkedPairTransport
import Atlas.Conway.OrthogonalFourGeometry
import Atlas.Mathieu.OctadMarkedPairTransport

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem octad_nonzero_coordinates (x : leech) (hx : x.val ∈ twoFourFamily 8 0)
    (i : Omega) (hi : x.val i ≠ 0) : x.val i = 2 ∨ x.val i = -2 := by
  obtain ⟨T,_,_,s,_,hs⟩ := minimum_octad_parameterization x hx
  have hiT : i ∈ T := by by_contra hn; exact hi (by rw [hs]; simp [signedSupport,hn])
  rw [hs]
  simp only [signedSupport,dif_pos hiT]
  split_ifs <;> norm_num

theorem orthogonal_containing_octad_transitive (i j : Omega) (hij : i ≠ j) (x y : leech)
    (hx : x.val ∈ twoFourFamily 8 0) (hy : y.val ∈ twoFourFamily 8 0)
    (hox : integerDot (minimumPairPlus i j).val x.val = 0)
    (hoy : integerDot (minimumPairPlus i j).val y.val = 0)
    (hxi : x.val i ≠ 0) (hyi : y.val i ≠ 0) :
    ∃ r : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j), r.val.val.val x = y := by
  have hsx : x.val i + x.val j = 0 := by rw [minimumPairPlus_dot] at hox; omega
  have hsy : y.val i + y.val j = 0 := by rw [minimumPairPlus_dot] at hoy; omega
  have hxj : x.val j ≠ 0 := by omega
  have hyj : y.val j ≠ 0 := by omega
  obtain ⟨S,hS,hCS,s,hps,hs⟩ := minimum_octad_parameterization x hx
  obtain ⟨T,hT,hCT,t,hpt,ht⟩ := minimum_octad_parameterization y hy
  have hiS : i ∈ S := by by_contra hn; exact hxi (by rw [hs]; simp [signedSupport,hn])
  have hjS : j ∈ S := by by_contra hn; exact hxj (by rw [hs]; simp [signedSupport,hn])
  have hiT : i ∈ T := by by_contra hn; exact hyi (by rw [ht]; simp [signedSupport,hn])
  have hjT : j ∈ T := by by_contra hn; exact hyj (by rw [ht]; simp [signedSupport,hn])
  have hOS := codeSupport_octad S hS hCS
  have hOT := codeSupport_octad T hT hCT
  obtain ⟨c,hc⟩ := octad_support_sign_realization S hS hCS s hps
  obtain ⟨d,hd⟩ := octad_support_sign_realization T hT hCT t hpt
  have hvals : x.val i = y.val i ∨ x.val j = y.val i := by
    have h1 := octad_nonzero_coordinates x hx i hxi
    have h2 := octad_nonzero_coordinates y hy i hyi
    omega
  rcases hvals with hv | hv
  · obtain ⟨g,hg,hgi,hgj⟩ := mathieu24_octad_marked_pair_transitive S T hOS hOT
      i j i j hiS hjS hij hiT hjT hij
    have hgi' : g.val.symm i = i := by rw [Equiv.symm_apply_eq]; exact hgi.symm
    have hgj' : g.val.symm j = j := by rw [Equiv.symm_apply_eq]; exact hgj.symm
    exact monomial_support_transport_marked_pair g 2 S T hg c d x y (hs.trans hc.symm)
      (ht.trans hd.symm) i j hij (Or.inl ⟨hgi,hgj⟩) (by rwa [hgi']) (by rw [hgj']; omega) hyi hyj
  · obtain ⟨g,hg,hgi,hgj⟩ := mathieu24_octad_marked_pair_transitive S T hOS hOT
      i j j i hiS hjS hij hjT hiT hij.symm
    have hgi' : g.val.symm i = j := by rw [Equiv.symm_apply_eq]; exact hgj.symm
    have hgj' : g.val.symm j = i := by rw [Equiv.symm_apply_eq]; exact hgi.symm
    exact monomial_support_transport_marked_pair g 2 S T hg c d x y (hs.trans hc.symm)
      (ht.trans hd.symm) i j hij (Or.inr ⟨hgi,hgj⟩) (by rwa [hgi']) (by rw [hgj']; omega) hyi hyj

end Atlas.Conway
