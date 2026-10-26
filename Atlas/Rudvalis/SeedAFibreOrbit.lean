import Atlas.Rudvalis.CodeGaussian
import Atlas.Rudvalis.MinimumAction

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators

noncomputable def seedConjugateHom : SignedCoordinates SeedCoordinate →* SignedCoordinates Coordinate where
  toFun := seedConjugateMonomial
  map_one' := by
    apply monomialHom_injective
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := seedTransportLinear.surjective w
    rw [seedConjugateMonomial_transport,map_one,map_one]
    rfl
  map_mul' a b := by
    apply monomialHom_injective
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := seedTransportLinear.surjective w
    change monomialHom (seedConjugateMonomial (a*b)) (seedTransportLinear v)=
      monomialHom (seedConjugateMonomial a*seedConjugateMonomial b) (seedTransportLinear v)
    rw [seedConjugateMonomial_transport,map_mul,map_mul]
    change seedTransportLinear (monomialHom a (monomialHom b v))=
      monomialHom (seedConjugateMonomial a) (monomialHom (seedConjugateMonomial b) (seedTransportLinear v))
    rw [seedConjugateMonomial_transport,seedConjugateMonomial_transport]

noncomputable def seedAOriginalU (m : ℕ) : SignedCoordinates SeedCoordinate :=
  seedPMonomial^m*seedUMonomial*(seedPMonomial^m)⁻¹
noncomputable def seedACodeU (m : ℕ) : codeGroup := codeP^m*codeU*(codeP^m)⁻¹

theorem seedACodeU_transport (m : ℕ) : (seedACodeU m).val=seedConjugateHom (seedAOriginalU m) := by
  simp only [seedAOriginalU,map_mul,map_pow,map_inv]
  rfl

noncomputable def seedAFourOriginal (b c : Bool) : SignedCoordinates SeedCoordinate :=
  (if b then seedAOriginalU 1 else 1)*(if c then seedAOriginalU 2 else 1)
noncomputable def seedAFourCode (b c : Bool) : codeGroup :=
  (if b then seedACodeU 1 else 1)*(if c then seedACodeU 2 else 1)
noncomputable def seedAFourWord (b c : Bool) : SeedCoordinate → ZMod 4 :=
  monomialHom (seedAFourOriginal b c) (fun z => (seedAArray z : ZMod 4))

theorem seedAFourCode_transport (b c : Bool) : (seedAFourCode b c).val=seedConjugateHom (seedAFourOriginal b c) := by
  cases b <;> cases c <;> simp [seedAFourCode,seedAFourOriginal,map_mul,seedACodeU_transport]

theorem seedAFour_action (b c : Bool) :
    monomialHom (seedAFourCode b c).val (quaternarySeed (0,0,0,0))=
      seedTransportLinear (seedAFourWord b c) := by
  rw [seedAFourCode_transport,quaternarySeed_transport]
  exact seedConjugateMonomial_transport _ _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem seedAFour_certificates (b c : Bool) :
    (∀z,reduceScalar (seedAFourWord b c z)=reduceScalar (seedAArray z : ZMod 4)) ∧
    seedAFourWord b c (0,0)*seedAFourWord b c (0,6)=(if b then -1 else 1) ∧
    seedAFourWord b c (0,0)*seedAFourWord b c (0,4)=(if c then -1 else 1) ∧
    (∀z,seedAArray z≠0 → (seedAFourWord b c z)^2=1) := by
  decide +kernel +revert

noncomputable def seedARowSign (v : E) : codeGroup :=
  ⟨SemidirectProduct.inl (Multiplicative.ofAdd (rowSigns (fun p => dot v p.val))),by
    apply (codeGroup_sign_mem _).mpr
    apply (rowSigns_mem_iff _).mpr
    obtain ⟨k,rfl⟩ := binaryLabel_bijective.surjective v
    change (∑ p : Point,dot (binaryLabel k) p.val • p.val)=0
    rw [← Equiv.sum_comp rowEquiv]
    decide +kernel +revert⟩

theorem seedARowSign_transport (v : E) (w : SeedCoordinate → ZMod 4) :
    monomialHom (seedARowSign v).val (seedTransportLinear w)=
      seedTransportLinear (fun z => signedScalar (dot v (rowLabel z.1).val) (w z)) := by
  funext z
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  change signedScalar (dot v (rowLabel r).val) (seedTransportLinear w (seedCoordinateEquiv (r,k)))=_
  rw [seedTransportLinear_apply,seedTransportLinear_apply]
  simp only [signedScalar]
  split <;> split <;> simp_all

noncomputable def seedAOrbitOriginal (v : E) (b c : Bool) : SeedCoordinate → ZMod 4 :=
  fun z => signedScalar (dot v (rowLabel z.1).val) (seedAFourWord b c z)
noncomputable def seedAOrbitElement (v : E) (b c : Bool) : codeGroup :=
  seedARowSign v*seedAFourCode b c

theorem seedAOrbit_action (v : E) (b c : Bool) :
    monomialHom (seedAOrbitElement v b c).val (quaternarySeed (0,0,0,0))=
      seedTransportLinear (seedAOrbitOriginal v b c) := by
  change monomialHom ((seedARowSign v).val*(seedAFourCode b c).val) _=_
  rw [map_mul]
  change monomialHom (seedARowSign v).val (monomialHom (seedAFourCode b c).val _) = _
  rw [seedAFour_action,seedARowSign_transport]
  rfl

private theorem scalar_pair (a : Bit) (x y : ZMod 4) :
    signedScalar a x*signedScalar a y=x*y := by
  simp only [signedScalar]
  split <;> simp

private theorem scalar_sign_injective (a b : Bit) (x : ZMod 4) (hx : x^2=1)
    (h : signedScalar a x=signedScalar b x) : a=b := by
  decide +kernel +revert

private theorem bool_sign_injective (a b : Bool)
    (h : (if a then (-1 : ZMod 4) else 1)=(if b then -1 else 1)) : a=b := by
  decide +kernel +revert

private theorem three_active_rows_separate (v w : E)
    (h0 : dot v (rowLabel 0).val=dot w (rowLabel 0).val)
    (h3 : dot v (rowLabel 3).val=dot w (rowLabel 3).val)
    (h5 : dot v (rowLabel 5).val=dot w (rowLabel 5).val) : v=w := by
  obtain ⟨i,rfl⟩ := binaryLabel_bijective.surjective v
  obtain ⟨j,rfl⟩ := binaryLabel_bijective.surjective w
  decide +kernel +revert

theorem seedAOrbitOriginal_injective :
    Function.Injective (fun t : E × Bool × Bool => seedAOrbitOriginal t.1 t.2.1 t.2.2) := by
  rintro ⟨v,b,c⟩ ⟨w,d,e⟩ h
  have hb : b=d := by
    apply bool_sign_injective
    have hh := congrArg (fun f : SeedCoordinate→ZMod 4 => f (0,0)*f (0,6)) h
    simp only [seedAOrbitOriginal,scalar_pair] at hh
    rwa [(seedAFour_certificates b c).2.1,(seedAFour_certificates d e).2.1] at hh
  have hc : c=e := by
    apply bool_sign_injective
    have hh := congrArg (fun f : SeedCoordinate→ZMod 4 => f (0,0)*f (0,4)) h
    simp only [seedAOrbitOriginal,scalar_pair] at hh
    rwa [(seedAFour_certificates b c).2.2.1,(seedAFour_certificates d e).2.2.1] at hh
  subst d
  subst e
  have hr (z : SeedCoordinate) (hz : seedAArray z≠0) :
      dot v (rowLabel z.1).val=dot w (rowLabel z.1).val :=
    scalar_sign_injective _ _ _ ((seedAFour_certificates b c).2.2.2 z hz) (congrFun h z)
  have hv : v=w := three_active_rows_separate v w
    (hr (0,0) (by decide)) (hr (3,1) (by decide)) (hr (5,1) (by decide))
  subst w
  rfl

private theorem transport_reduce_congr (v w : SeedCoordinate→ZMod 4)
    (h : ∀z,reduceScalar (v z)=reduceScalar (w z)) :
    reduce (seedTransportLinear v)=reduce (seedTransportLinear w) := by
  funext z
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  change reduceScalar (seedTransportLinear v (seedCoordinateEquiv (r,k)))=
    reduceScalar (seedTransportLinear w (seedCoordinateEquiv (r,k)))
  rw [seedTransportLinear_apply,seedTransportLinear_apply]
  split <;> simp only [map_neg,h]

theorem seedAOrbit_reduce (v : E) (b c : Bool) :
    reduce (monomialHom (seedAOrbitElement v b c).val (quaternarySeed (0,0,0,0)))=
      reduce (quaternarySeed (0,0,0,0)) := by
  rw [seedAOrbit_action,quaternarySeed_transport]
  apply transport_reduce_congr
  intro z
  change reduceScalar (signedScalar (dot v (rowLabel z.1).val) (seedAFourWord b c z))=
    reduceScalar (seedAArray z : ZMod 4)
  have hr : ∀a : Bit,∀x : ZMod 4,reduceScalar (signedScalar a x)=reduceScalar x := by decide +kernel
  rw [hr]
  exact (seedAFour_certificates b c).1 z

noncomputable def seedAOrbitLift (t : E × Bool × Bool) :
    minimumLift (reduce (quaternarySeed (0,0,0,0))) :=
  ⟨⟨monomialHom (seedAOrbitElement t.1 t.2.1 t.2.2).val (quaternarySeed (0,0,0,0)),
    ((seedAOrbitElement t.1 t.2.1 t.2.2).prop _).mp (quaternaryCode_seed _)⟩,
      (monomial_euclideanWeight _ _).trans (quaternary_base_seed_weight 0),
      seedAOrbit_reduce _ _ _⟩

theorem seedAOrbitLift_injective : Function.Injective seedAOrbitLift := by
  intro a b h
  have hh := congrArg (fun w : minimumLift (reduce (quaternarySeed (0,0,0,0))) => w.val.val) h
  change monomialHom (seedAOrbitElement a.1 a.2.1 a.2.2).val _=
    monomialHom (seedAOrbitElement b.1 b.2.1 b.2.2).val _ at hh
  rw [seedAOrbit_action,seedAOrbit_action] at hh
  exact seedAOrbitOriginal_injective (seedTransportLinear.injective hh)

theorem seedAOrbitLift_surjective_of_card
    (hcard : Nat.card (minimumLift (reduce (quaternarySeed (0,0,0,0))))=32) :
    Function.Surjective seedAOrbitLift := by
  apply (Nat.bijective_iff_injective_and_card seedAOrbitLift).mpr
    ⟨seedAOrbitLift_injective,?_⟩ |>.2
  rw [hcard]
  simp [Nat.card_eq_fintype_card,E,Bit,ZMod.card]

theorem seedA_fibre_transitive_of_card
    (hcard : Nat.card (minimumLift (reduce (quaternarySeed (0,0,0,0))))=32)
    (w : minimumLift (reduce (quaternarySeed (0,0,0,0)))) :
    ∃g : codeGroup,monomialHom g.val (quaternarySeed (0,0,0,0))=w.val.val := by
  obtain ⟨⟨v,b,c⟩,h⟩ := seedAOrbitLift_surjective_of_card hcard w
  exact ⟨seedAOrbitElement v b c,congrArg (fun u => u.val.val) h⟩

end Atlas.Rudvalis



