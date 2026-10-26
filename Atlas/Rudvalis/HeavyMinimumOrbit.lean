import Atlas.Rudvalis.HeavyLiftCount

/-! The heavy minimum words form one orbit of the actual signed code group. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem heavySeed_signedLift_sign_transitive
    (v w : SignedLift quaternaryCode heavySeedResidue) :
    ∃ s : signPatterns,signChange s.val v.val.val=w.val.val := by
  obtain ⟨t,ht⟩ := (signedLiftMap_bijective quaternaryCode binaryTorsion quaternaryCode_torsion
    heavySeedResidue v).2 w
  let a := heavyShortEquiv t
  let s : signPatterns := ⟨rowSigns a.val,(rowSigns_mem_iff a.val).mpr a.prop⟩
  refine ⟨s,?_⟩
  have he : v.val.val+double t.val=w.val.val := congrArg (fun u => u.val.val) ht
  rw [signChange_difference,v.prop.1]
  have hs : (fun z => s.val z*heavySeedResidue z)=t.val := by
    funext z
    exact (heavyShort_block_constant t z).symm
  rw [hs,←he]
  have hn : -double t.val=double t.val := by
    funext z
    have h : ∀ b : Binary,-doubleScalar b=doubleScalar b := by decide +kernel
    exact h _
  rw [sub_eq_add_neg,hn]

theorem heavySeed_signedLift_code_transitive
    (v w : SignedLift quaternaryCode heavySeedResidue) :
    ∃ g : codeGroup,monomialHom g.val v.val.val=w.val.val := by
  obtain ⟨s,hs⟩ := heavySeed_signedLift_sign_transitive v w
  exact ⟨⟨SemidirectProduct.inl (Multiplicative.ofAdd s.val),(codeGroup_sign_mem s.val).mpr s.prop⟩,hs⟩

noncomputable def heavySeedSignedLift : SignedLift quaternaryCode heavySeedResidue :=
  minimumSignedLiftEquiv heavySeedResidue heavySeedResidue_weight heavySeedMinimumLift

theorem heavy_transported_signedLift_orbit (g : codeGroup)
    (w : SignedLift quaternaryCode (heavySeedResidue ∘ g.val.right.symm)) :
    ∃ h : codeGroup,monomialHom h.val heavySeedSignedLift.val.val=w.val.val := by
  let e := signedLiftActionEquiv g heavySeedResidue
  obtain ⟨h,hh⟩ := heavySeed_signedLift_code_transitive heavySeedSignedLift (e.symm w)
  refine ⟨g*h,?_⟩
  change monomialHom (g.val*h.val) heavySeedSignedLift.val.val=w.val.val
  rw [map_mul]
  change monomialHom g.val (monomialHom h.val heavySeedSignedLift.val.val)=w.val.val
  rw [hh]
  exact congrArg (fun u => u.val.val) (e.apply_symm_apply w)

theorem heavy_minimum_seed_orbit (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hweight : euclideanWeight w=16) (hheavy : hasNonzeroQuadraticPart (reduce w)) :
    ∃ g : codeGroup,monomialHom g.val heavySeedSignedLift.val.val=w := by
  obtain ⟨a,hc,ha⟩ := hheavy
  have hd := quaternary_minimum_residue_weight w hw hweight
  obtain ⟨p,hp⟩ := heavySupport_seed_orbit a.1 a.2.1 a.2.2 hc (ha ▸ hd)
  have hr : reduce w=heavySeedResidue ∘ p.val := ha.symm.trans hp
  obtain ⟨g,hg⟩ := codePermutationHom_surjective p⁻¹
  have he : g.val.right=p.val⁻¹ := congrArg Subtype.val hg
  have hr2 : reduce w=heavySeedResidue ∘ g.val.right.symm := by rw [he]; exact hr
  let wlift : SignedLift quaternaryCode (heavySeedResidue ∘ g.val.right.symm) :=
    ⟨⟨w,hw⟩,hr2,quaternary_minimum_no_twos w hw hweight⟩
  exact heavy_transported_signedLift_orbit g wlift

theorem heavy_minimum_transitive (v w : QuaternaryWord)
    (hv : v∈quaternaryCode) (hw : w∈quaternaryCode)
    (hv16 : euclideanWeight v=16) (hw16 : euclideanWeight w=16)
    (hvh : hasNonzeroQuadraticPart (reduce v)) (hwh : hasNonzeroQuadraticPart (reduce w)) :
    ∃ g : codeGroup,monomialHom g.val v=w := by
  obtain ⟨g,hg⟩ := heavy_minimum_seed_orbit v hv hv16 hvh
  obtain ⟨h,hh⟩ := heavy_minimum_seed_orbit w hw hw16 hwh
  refine ⟨h*g⁻¹,?_⟩
  change monomialHom (h.val*g.val⁻¹) v=w
  rw [map_mul,←hg]
  simpa using hh

end Atlas.Rudvalis
