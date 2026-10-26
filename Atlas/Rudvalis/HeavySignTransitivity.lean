import Atlas.Rudvalis.HeavyMinimumOrbit
import Atlas.Rudvalis.CoordinateCrossAction

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem heavy_signedLift_sign_transitive (d : BinaryWord)
    (hd : hasNonzeroQuadraticPart d) (hd16 : hammingNorm d=16)
    (v w : SignedLift quaternaryCode d) :
    ∃k : codeGroup,k.val.right=1 ∧ monomialHom k.val v.val.val=w.val.val := by
  obtain ⟨a,hc,ha⟩ := hd
  obtain ⟨p,hp⟩ := heavySupport_seed_orbit a.1 a.2.1 a.2.2 hc (ha ▸ hd16)
  have hr : d=heavySeedResidue ∘ p.val := ha.symm.trans hp
  obtain ⟨g,hg⟩ := codePermutationHom_surjective p⁻¹
  have he : g.val.right=p.val⁻¹ := congrArg Subtype.val hg
  have hr2 : d=heavySeedResidue ∘ g.val.right.symm := by rw [he]; exact hr
  clear ha hr
  subst d
  let e := signedLiftActionEquiv g heavySeedResidue
  obtain ⟨s,hs⟩ := heavySeed_signedLift_sign_transitive (e.symm v) (e.symm w)
  let h : codeGroup := ⟨SemidirectProduct.inl (Multiplicative.ofAdd s.val),
    (codeGroup_sign_mem s.val).mpr s.prop⟩
  have hh : monomialHom h.val (e.symm v).val.val=(e.symm w).val.val := hs
  refine ⟨g*h*g⁻¹,?_,?_⟩
  · change g.val.right*1*g.val.right⁻¹=1
    simp
  · have hv : monomialHom g.val (e.symm v).val.val=v.val.val :=
      congrArg (fun u => u.val.val) (e.apply_symm_apply v)
    have hw : monomialHom g.val (e.symm w).val.val=w.val.val :=
      congrArg (fun u => u.val.val) (e.apply_symm_apply w)
    change monomialHom (g.val*h.val*g.val⁻¹) v.val.val=w.val.val
    rw [map_mul,map_mul]
    change monomialHom g.val (monomialHom h.val (monomialHom g.val⁻¹ v.val.val))=w.val.val
    rw [←hv]
    simp only [map_inv]
    change monomialHom g.val (monomialHom h.val ((monomialHom g.val).symm
      (monomialHom g.val (e.symm v).val.val)))=w.val.val
    rw [LinearEquiv.symm_apply_apply]
    rw [hh,hw]

theorem codeGroup_sign_fixes_coordinateCross (g : codeGroup) (hg : g.val.right=1)
    (i : Coordinate) : g • coordinateCross i=coordinateCross i := by
  rw [coordinateCross_action,hg]
  rfl

end Atlas.Rudvalis
