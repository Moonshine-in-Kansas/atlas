import Atlas.Rudvalis.HexadEmbedding

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

/-- The literal v33 V word, built from already verified signed code automorphisms. -/
noncomputable def codeV : codeGroup :=
  codeRho*codeSigma*seedACodeU 0*seedACodeU 4*seedACodeU 3*seedACodeU 1*seedACodeU 2
noncomputable def seedVMonomial : SignedCoordinates SeedCoordinate :=
  seedUnitMonomial 1*seedUnitMonomial 2*seedAOriginalU 0*seedAOriginalU 4*
    seedAOriginalU 3*seedAOriginalU 1*seedAOriginalU 2

theorem codeV_transport : codeV.val=seedConjugateHom seedVMonomial := by
  simp only [codeV,seedVMonomial,map_mul,Subgroup.coe_mul,seedACodeU_transport]
  rfl

noncomputable def seedIntegerRational (v : SeedCoordinate→ℤ) : RationalSpace :=
  seedTransportLinear (fun i => (v i:ℚ))

theorem rationalMonomial_conjugate_integer (g : SignedCoordinates SeedCoordinate)
    (v : SeedCoordinate→ℤ) :
    rationalMonomialHom (seedConjugateHom g) (seedIntegerRational v)=
      seedIntegerRational (liftedCoordinateHom g v) := by
  change liftedCoordinateHom (seedConjugateMonomial g) (seedTransportLinear (fun i=>(v i:ℚ)))=_
  rw [seedConjugate_lifted_transport]
  apply congrArg seedTransportLinear
  funext i
  change liftedSign (g.left.toAdd i) ((v (g.right.symm i):ℤ):ℚ)=
    ((liftedSign (g.left.toAdd i) (v (g.right.symm i)):ℤ):ℚ)
  simp [liftedSign]

end Atlas.Rudvalis
