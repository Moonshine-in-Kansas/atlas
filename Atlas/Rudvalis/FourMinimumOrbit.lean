import Atlas.Rudvalis.SeedAFibreOrbit
import Atlas.Rudvalis.FourLiftCount

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem seedA_fibre_transitive (w : minimumLift fourSeedResidue) :
    ∃g : codeGroup,monomialHom g.val (quaternarySeed (0,0,0,0))=w.val.val := by
  have hr : reduce (quaternarySeed (0,0,0,0))=fourSeedResidue := fourSeedMinimumLift.prop.2
  have hc : Nat.card (minimumLift (reduce (quaternarySeed (0,0,0,0))))=32 := by
    rw [hr]; exact fourSeed_minimum_lifts_card
  let v : minimumLift (reduce (quaternarySeed (0,0,0,0))) :=
    ⟨w.val,w.prop.1,w.prop.2.trans hr.symm⟩
  exact seedA_fibre_transitive_of_card hc v

theorem seedA_signedLift_orbit (w : SignedLift quaternaryCode fourSeedResidue) :
    ∃g : codeGroup,monomialHom g.val (quaternarySeed (0,0,0,0))=w.val.val :=
  seedA_fibre_transitive ((minimumSignedLiftEquiv fourSeedResidue fourSeedResidue_weight).symm w)

theorem fourthSeed_signedLift_orbit (w : SignedLift quaternaryCode fourPlaneSeedResidue) :
    ∃g : codeGroup,monomialHom g.val (quaternarySeed (0,0,0,0))=w.val.val := by
  have hd : fourPlaneSeedResidue=fourSeedResidue ∘ (codeP^3).val.right.symm := by
    have h := congrArg reduce codeP_cube_seedA
    rw [fourthSeed_residue] at h
    change reduce (monomialAction (codeP^3).val (quaternarySeed (0,0,0,0)))=_ at h
    have ha : reduce (quaternarySeed (0,0,0,0))=fourSeedResidue := fourSeedMinimumLift.prop.2
    rw [monomialAction_reduce,ha] at h
    exact h.symm
  let v : SignedLift quaternaryCode (fourSeedResidue ∘ (codeP^3).val.right.symm) :=
    ⟨w.val,w.prop.1.trans hd,w.prop.2⟩
  let e := signedLiftActionEquiv (codeP^3) fourSeedResidue
  obtain ⟨g,hg⟩ := seedA_signedLift_orbit (e.symm v)
  refine ⟨codeP^3*g,?_⟩
  change monomialHom ((codeP^3).val*g.val) _=w.val.val
  rw [map_mul]
  change monomialHom (codeP^3).val (monomialHom g.val _)=w.val.val
  rw [hg]
  exact congrArg (fun u => u.val.val) (e.apply_symm_apply v)

theorem four_transported_signedLift_orbit (g : codeGroup)
    (w : SignedLift quaternaryCode (fourPlaneSeedResidue ∘ g.val.right.symm)) :
    ∃h : codeGroup,monomialHom h.val (quaternarySeed (0,0,0,0))=w.val.val := by
  let e := signedLiftActionEquiv g fourPlaneSeedResidue
  obtain ⟨h,hh⟩ := fourthSeed_signedLift_orbit (e.symm w)
  refine ⟨g*h,?_⟩
  change monomialHom (g.val*h.val) _=w.val.val
  rw [map_mul]
  change monomialHom g.val (monomialHom h.val _)=w.val.val
  rw [hh]
  exact congrArg (fun u => u.val.val) (e.apply_symm_apply w)

theorem four_minimum_seed_orbit (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hweight : euclideanWeight w=16) (hfour : admissibleFourSupport (reduce w)) :
    ∃g : codeGroup,monomialHom g.val (quaternarySeed (0,0,0,0))=w := by
  obtain ⟨p,hp⟩ := fourSupport_seed_orbit (reduce w) hfour
  obtain ⟨g,hg⟩ := codePermutationHom_surjective p⁻¹
  have he : g.val.right=p.val⁻¹ := congrArg Subtype.val hg
  have hr : reduce w=fourPlaneSeedResidue ∘ g.val.right.symm := by rw [he]; exact hp
  exact four_transported_signedLift_orbit g
    ⟨⟨w,hw⟩,hr,quaternary_minimum_no_twos w hw hweight⟩

theorem four_minimum_transitive (v w : QuaternaryWord)
    (hv : v∈quaternaryCode) (hw : w∈quaternaryCode)
    (hv16 : euclideanWeight v=16) (hw16 : euclideanWeight w=16)
    (hvf : admissibleFourSupport (reduce v)) (hwf : admissibleFourSupport (reduce w)) :
    ∃g : codeGroup,monomialHom g.val v=w := by
  obtain ⟨g,hg⟩ := four_minimum_seed_orbit v hv hv16 hvf
  obtain ⟨h,hh⟩ := four_minimum_seed_orbit w hw hw16 hwf
  refine ⟨h*g⁻¹,?_⟩
  change monomialHom (h.val*g.val⁻¹) v=w
  rw [map_mul,←hg]
  simpa using hh

theorem codeAction_activeBlocks_card (g : codeGroup) (w : QuaternaryWord) :
    (activeBlocks (reduce (monomialHom g.val w))).card=(activeBlocks (reduce w)).card := by
  change (activeBlocks (reduce (monomialAction g.val w))).card=_
  rw [monomialAction_reduce]
  change (activeBlocks (reduce w ∘ ((codePermutationHom g).val⁻¹ : Equiv.Perm Coordinate))).card=_
  rw [activeBlocks_permute,Finset.card_image_of_injective _ (binaryBlockHom (codePermutationHom g)).injective]

theorem fourSeed_activeBlocks_card : (activeBlocks fourSeedResidue).card=4 := by
  decide +kernel

theorem four_minimum_activeBlocks_card (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hweight : euclideanWeight w=16) (hfour : admissibleFourSupport (reduce w)) :
    (activeBlocks (reduce w)).card=4 := by
  obtain ⟨g,hg⟩ := four_minimum_seed_orbit w hw hweight hfour
  rw [←hg,codeAction_activeBlocks_card]
  have hr : reduce (quaternarySeed (0,0,0,0))=fourSeedResidue := fourSeedMinimumLift.prop.2
  rw [hr,fourSeed_activeBlocks_card]

theorem heavy_activeBlocks_card (w : BinaryWord) (hw : hasNonzeroQuadraticPart w) :
    (activeBlocks w).card=7 := by
  obtain ⟨a,hc,ha⟩ := hw
  rw [←ha,activeBlocks_quadratic a hc]
  simp

theorem four_heavy_minimum_distinct_orbits (v w : QuaternaryWord)
    (hv : v∈quaternaryCode) (hv16 : euclideanWeight v=16)
    (hvf : admissibleFourSupport (reduce v)) (hwh : hasNonzeroQuadraticPart (reduce w)) :
    ∀g : codeGroup,monomialHom g.val v≠w := by
  intro g hg
  have h := codeAction_activeBlocks_card g v
  rw [hg,four_minimum_activeBlocks_card v hv hv16 hvf,heavy_activeBlocks_card _ hwh] at h
  omega

end Atlas.Rudvalis

