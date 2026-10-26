import Atlas.Rudvalis.SecondFrame
import Atlas.Rudvalis.SeedFrobenius

/-! The actual Frobenius element has the prescribed labeled action on the second frame. -/
namespace Atlas.Rudvalis

theorem secondFrameT_data (r : Fin 7) (k : Fin 8) :
    seedTOrbitIndex (secondFrameOrbitIndex (r,k))=
      secondFrameOrbitIndex (seedDoubleRow r,seedTIndexEquiv.symm k) ∧
    secondFrameSign k=secondFrameSign (seedTIndexEquiv.symm k) := by
  decide +kernel +revert

theorem integerMonomial_T_seed (t : SeedOrbitIndex) :
    integerMonomial codeT.val (seedOrbitWord t)=seedOrbitWord (seedTOrbitIndex t) := by
  simp only [seedOrbitWord,signedSeedTransport_eq_linear]
  change liftedCoordinateHom (seedConjugateMonomial seedTMonomial)
    (seedTransportLinear (seedOrbitOriginal t))=seedTransportLinear (seedOrbitOriginal (seedTOrbitIndex t))
  rw [seedConjugate_lifted_transport]
  apply congrArg seedTransportLinear
  exact seedT_orbit t

theorem secondFrameInteger_T (r : Fin 7) (k : Fin 8) :
    integerMonomial codeT.val (secondFrameInteger (r,k))=
      secondFrameInteger (seedDoubleRow r,seedTIndexEquiv.symm k) := by
  change liftedCoordinateHom codeT.val
    (secondFrameSign k • seedOrbitWord (secondFrameOrbitIndex (r,k)))=_
  rw [map_smul]
  change secondFrameSign k • integerMonomial codeT.val (seedOrbitWord (secondFrameOrbitIndex (r,k)))=_
  rw [integerMonomial_T_seed,(secondFrameT_data r k).1,(secondFrameT_data r k).2]
  rfl

theorem secondFrame_T (r : Fin 7) (k : Fin 8) :
    rationalMonomialHom codeT.val (secondFrame (r,k))=
      secondFrame (seedDoubleRow r,seedTIndexEquiv.symm k) := by
  change rationalMonomialHom codeT.val (halfCoordinates (secondFrameInteger (r,k)))=_
  rw [rationalMonomial_half,secondFrameInteger_T]
  rfl

end Atlas.Rudvalis
