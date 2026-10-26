import Atlas.Rudvalis.SecondFrameGaussian

namespace Atlas.Rudvalis

noncomputable def codeUnit (u : Fin 8) : codeGroup :=
  ⟨rudvalisUnitMonomial u,rudvalisUnitMonomial_mem u⟩

private theorem secondFrameUnit_data (u : Fin 8) (r : Fin 7) (k : Fin 8) :
    seedUnitOrbitIndex u (secondFrameOrbitIndex (r,k))=
      secondFrameOrbitIndex (r,seedUnitSource u k) ∧
    (if seedUnitProductNegative u (seedPackedUnit
      (secondFrameOrbitIndex (r,k)).2.1 (secondFrameOrbitIndex (r,k)).2.2.1)
      then -secondFrameSign k else secondFrameSign k)=
      (if seedUnitSign u (seedUnitSource u k) then -secondFrameSign (seedUnitSource u k)
       else secondFrameSign (seedUnitSource u k)) := by
  decide +kernel +revert

theorem integerMonomial_unit_seedOrbit (u : Fin 8) (t : SeedOrbitIndex) :
    integerMonomial (rudvalisUnitMonomial u) (seedOrbitWord t)=
      if seedUnitProductNegative u (seedPackedUnit t.2.1 t.2.2.1) then
        -seedOrbitWord (seedUnitOrbitIndex u t) else seedOrbitWord (seedUnitOrbitIndex u t) := by
  change integerMonomial (rudvalisUnitMonomial u) (signedSeedTransport (seedOrbitOriginal t))=_
  rw [integerMonomial_unit_transport,seedOrbitOriginal_unit]
  split <;> simp_all [seedOrbitWord,signedSeedTransport_eq_linear]

theorem secondFrameInteger_unit (u : Fin 8) (r : Fin 7) (k : Fin 8) :
    integerMonomial (codeUnit u).val (secondFrameInteger (r,k))=
      if seedUnitSign u (seedUnitSource u k) then -secondFrameInteger (r,seedUnitSource u k)
      else secondFrameInteger (r,seedUnitSource u k) := by
  change liftedCoordinateHom (codeUnit u).val (secondFrameSign k • seedOrbitWord (secondFrameOrbitIndex (r,k)))=_
  rw [map_smul]
  change secondFrameSign k • integerMonomial (rudvalisUnitMonomial u) (seedOrbitWord (secondFrameOrbitIndex (r,k)))=_
  rw [integerMonomial_unit_seedOrbit,(secondFrameUnit_data u r k).1]
  have hs := (secondFrameUnit_data u r k).2
  unfold secondFrameInteger
  split_ifs at hs ⊢ <;>
    simpa only [smul_neg,neg_smul] using congrArg
      (fun n : ℤ => n • seedOrbitWord (secondFrameOrbitIndex (r,seedUnitSource u k))) hs

theorem secondFrame_unit (u : Fin 8) (r : Fin 7) (k : Fin 8) :
    rationalMonomialHom (codeUnit u).val (secondFrame (r,k))=
      if seedUnitSign u (seedUnitSource u k) then -secondFrame (r,seedUnitSource u k)
      else secondFrame (r,seedUnitSource u k) := by
  change rationalMonomialHom (codeUnit u).val (halfCoordinates (secondFrameInteger (r,k)))=_
  rw [rationalMonomial_half,secondFrameInteger_unit]
  split <;> simp_all [secondFrame]

end Atlas.Rudvalis
