import Atlas.Rudvalis.FourLocalWords
import Atlas.Rudvalis.FourSeedLifts

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
set_option maxRecDepth 16384

noncomputable def fourLocalSignsOriginal (b c : Bool) : SignedCoordinates SeedCoordinate :=
  (if b then fourLocalOriginalA else 1)*(if c then fourLocalOriginalB else 1)
noncomputable def fourLocalSignsCode (b c : Bool) : codeGroup :=
  (if b then fourLocalCodeA else 1)*(if c then fourLocalCodeB else 1)
noncomputable def fourLocalSignsWord (b c : Bool) : SeedCoordinate → ZMod 4 :=
  monomialHom (fourLocalSignsOriginal b c) fourLocalSeed

theorem fourLocalSigns_transport (b c : Bool) :
    (fourLocalSignsCode b c).val=seedConjugateHom (fourLocalSignsOriginal b c) := by
  cases b <;> cases c <;> simp [fourLocalSignsCode,fourLocalSignsOriginal,
    fourLocalCodeA_transport,fourLocalCodeB_transport,map_mul]

theorem fourLocalSeed_transport : quaternarySeed (3,0,0,0)=seedTransportLinear fourLocalSeed := by
  rw [←codeP_cube_seedA,quaternarySeed_transport]
  have h : (codeP^3).val=seedConjugateHom (seedPMonomial^3) := by rw [map_pow]; rfl
  rw [h]
  exact seedConjugateMonomial_transport _ _

set_option maxHeartbeats 2000000 in
theorem fourLocalSigns_certificates (b c : Bool) :
    (∀z,reduceScalar (fourLocalSignsWord b c z)=reduceScalar (fourLocalSeed z)) ∧
    fourLocalSignsWord b c (1,1)*fourLocalSignsWord b c (1,3)=(if b then -1 else 1) ∧
    fourLocalSignsWord b c (1,3)*fourLocalSignsWord b c (1,4)=(if c then 1 else -1) ∧
    (∀z,fourLocalSeed z≠0 → (fourLocalSignsWord b c z)^2=1) := by
  decide +kernel +revert

noncomputable def fourLocalOrbitOriginal (v : E) (b c : Bool) : SeedCoordinate → ZMod 4 :=
  fun z => signedScalar (dot v (rowLabel z.1).val) (fourLocalSignsWord b c z)
noncomputable def fourLocalOrbitElement (v : E) (b c : Bool) : codeGroup :=
  seedARowSign v*fourLocalSignsCode b c

theorem fourLocalOrbit_action (v : E) (b c : Bool) :
    monomialHom (fourLocalOrbitElement v b c).val (quaternarySeed (3,0,0,0))=
      seedTransportLinear (fourLocalOrbitOriginal v b c) := by
  change monomialHom ((seedARowSign v).val*(fourLocalSignsCode b c).val) _=_
  rw [map_mul]
  change monomialHom (seedARowSign v).val (monomialHom (fourLocalSignsCode b c).val _) = _
  rw [fourLocalSigns_transport,fourLocalSeed_transport]
  change monomialHom (seedARowSign v).val (monomialHom (seedConjugateMonomial (fourLocalSignsOriginal b c)) (seedTransportLinear fourLocalSeed))=_
  rw [seedConjugateMonomial_transport,seedARowSign_transport]
  rfl

private theorem local_scalar_pair (a : Bit) (x y : ZMod 4) :
    signedScalar a x*signedScalar a y=x*y := by
  simp only [signedScalar]
  split <;> simp

private theorem local_scalar_sign_injective (a b : Bit) (x : ZMod 4) (hx : x^2=1)
    (h : signedScalar a x=signedScalar b x) : a=b := by decide +kernel +revert

private theorem local_bool_sign_injective (a b : Bool)
    (h : (if a then (-1 : ZMod 4) else 1)=(if b then -1 else 1)) : a=b := by decide +kernel +revert

private theorem local_three_rows_separate (v w : E)
    (h1 : dot v (rowLabel 1).val=dot w (rowLabel 1).val)
    (h2 : dot v (rowLabel 2).val=dot w (rowLabel 2).val)
    (h3 : dot v (rowLabel 3).val=dot w (rowLabel 3).val) : v=w := by
  obtain ⟨i,rfl⟩ := binaryLabel_bijective.surjective v
  obtain ⟨j,rfl⟩ := binaryLabel_bijective.surjective w
  decide +kernel +revert

theorem fourLocalOrbitOriginal_injective :
    Function.Injective (fun t : E × Bool × Bool => fourLocalOrbitOriginal t.1 t.2.1 t.2.2) := by
  rintro ⟨v,b,c⟩ ⟨w,d,e⟩ h
  have hb : b=d := by
    apply local_bool_sign_injective
    have hh := congrArg (fun f : SeedCoordinate→ZMod 4 => f (1,1)*f (1,3)) h
    simp only [fourLocalOrbitOriginal,local_scalar_pair] at hh
    rwa [(fourLocalSigns_certificates b c).2.1,(fourLocalSigns_certificates d e).2.1] at hh
  have hc : c=e := by
    have hh := congrArg (fun f : SeedCoordinate→ZMod 4 => f (1,3)*f (1,4)) h
    simp only [fourLocalOrbitOriginal,local_scalar_pair] at hh
    rw [(fourLocalSigns_certificates b c).2.2.1,(fourLocalSigns_certificates d e).2.2.1] at hh
    have hi : ∀c e : Bool, (if c then (1 : ZMod 4) else -1)=(if e then 1 else -1) → c=e := by decide +kernel
    exact hi c e hh
  subst d
  subst e
  have hr (z : SeedCoordinate) (hz : fourLocalSeed z≠0) :
      dot v (rowLabel z.1).val=dot w (rowLabel z.1).val :=
    local_scalar_sign_injective _ _ _ ((fourLocalSigns_certificates b c).2.2.2 z hz) (congrFun h z)
  have hv : v=w := local_three_rows_separate v w
    (hr (1,1) (by decide +kernel)) (hr (2,1) (by decide +kernel)) (hr (3,0) (by decide +kernel))
  subst w
  rfl

theorem fourLocalOrbit_reduce (v : E) (b c : Bool) :
    reduce (monomialHom (fourLocalOrbitElement v b c).val (quaternarySeed (3,0,0,0)))=fourPlaneSeedResidue := by
  rw [←fourthSeed_residue,fourLocalOrbit_action,fourLocalSeed_transport]
  funext z
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  change reduceScalar (seedTransportLinear (fourLocalOrbitOriginal v b c) (seedCoordinateEquiv (r,k)))=
    reduceScalar (seedTransportLinear fourLocalSeed (seedCoordinateEquiv (r,k)))
  rw [seedTransportLinear_apply,seedTransportLinear_apply]
  have hr : ∀a : Bit,∀x : ZMod 4,reduceScalar (signedScalar a x)=reduceScalar x := by decide +kernel
  have hh := (fourLocalSigns_certificates b c).1 (r,signedPositionIndex k)
  simp only [fourLocalOrbitOriginal]
  split <;> simp only [map_neg,hr,hh]

noncomputable def fourLocalOrbitLift (t : E × Bool × Bool) : minimumLift fourPlaneSeedResidue :=
  ⟨⟨monomialHom (fourLocalOrbitElement t.1 t.2.1 t.2.2).val (quaternarySeed (3,0,0,0)),
    ((fourLocalOrbitElement t.1 t.2.1 t.2.2).prop _).mp (quaternaryCode_seed _)⟩,
    (monomial_euclideanWeight _ _).trans fourthSeed_weight,fourLocalOrbit_reduce _ _ _⟩

theorem fourLocalOrbitLift_injective : Function.Injective fourLocalOrbitLift := by
  intro a b h
  have hh := congrArg (fun w : minimumLift fourPlaneSeedResidue => w.val.val) h
  change monomialHom (fourLocalOrbitElement a.1 a.2.1 a.2.2).val _=
    monomialHom (fourLocalOrbitElement b.1 b.2.1 b.2.2).val _ at hh
  rw [fourLocalOrbit_action,fourLocalOrbit_action] at hh
  exact fourLocalOrbitOriginal_injective (seedTransportLinear.injective hh)

theorem fourLocalOrbitLift_surjective : Function.Surjective fourLocalOrbitLift := by
  apply (Nat.bijective_iff_injective_and_card fourLocalOrbitLift).mpr
    ⟨fourLocalOrbitLift_injective,?_⟩ |>.2
  rw [fourPlaneSeed_minimum_lifts_card]
  simp [Nat.card_eq_fintype_card,E,Bit,ZMod.card]

theorem fourLocalOrbitElement_fix (v : E) (b c : Bool) :
    fourLocalOrbitElement v b c • coordinateCross (originalCoordinateEquiv (0,1))=
      coordinateCross (originalCoordinateEquiv (0,1)) := by
  have hr : seedARowSign v • coordinateCross (originalCoordinateEquiv (0,1))=
      coordinateCross (originalCoordinateEquiv (0,1)) := by
    rw [coordinateCross_action]
    rfl
  rw [fourLocalOrbitElement,mul_smul]
  have hs : fourLocalSignsCode b c • coordinateCross (originalCoordinateEquiv (0,1))=
      coordinateCross (originalCoordinateEquiv (0,1)) := by
    cases b <;> cases c <;>
      simp only [fourLocalSignsCode,Bool.false_eq_true,ite_false,ite_true,
        mul_smul,one_smul,fourLocalCode_fix.2.1,fourLocalCode_fix.2.2]
  rw [hs,hr]

theorem fourLocal_fibre_transitive (w : minimumLift fourPlaneSeedResidue) :
    ∃g : MulAction.stabilizer codeGroup (coordinateCross (originalCoordinateEquiv (0,1))),
      monomialHom g.val.val (quaternarySeed (3,0,0,0))=w.val.val := by
  obtain ⟨⟨v,b,c⟩,h⟩ := fourLocalOrbitLift_surjective w
  refine ⟨⟨fourLocalOrbitElement v b c,fourLocalOrbitElement_fix v b c⟩,?_⟩
  exact congrArg (fun u => u.val.val) h

end Atlas.Rudvalis
