import Atlas.Rudvalis.SecondFrameBasis
import Atlas.Rudvalis.SeedIntegralTransport
import Atlas.Rudvalis.SeedAFibreOrbit

/-! The literal W word and the single six-vector embedding certificate. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

noncomputable def seedOriginalRowSign (v : E) : SignedCoordinates SeedCoordinate :=
  SemidirectProduct.inl (Multiplicative.ofAdd (fun z => dot v (rowLabel z.1).val))

theorem seedARowSign_conjugate (v : E) :
    (seedARowSign v).val=seedConjugateHom (seedOriginalRowSign v) := by
  apply monomialHom_injective
  apply LinearEquiv.ext
  intro w
  obtain ⟨w,rfl⟩ := seedTransportLinear.surjective w
  rw [seedARowSign_transport]
  change _=monomialHom (seedConjugateMonomial (seedOriginalRowSign v)) (seedTransportLinear w)
  rw [seedConjugateMonomial_transport]
  rfl

noncomputable def seedWMonomial : SignedCoordinates SeedCoordinate :=
  seedOriginalRowSign (binaryLabel 5)*seedUnitMonomial 2*
    seedAOriginalU 1*seedAOriginalU 2*seedAOriginalU 3

noncomputable def codeW : codeGroup := seedARowSign (binaryLabel 5)*codeSigma*
  seedACodeU 1*seedACodeU 2*seedACodeU 3

theorem codeW_transport : codeW.val=seedConjugateHom seedWMonomial := by
  simp only [codeW,seedWMonomial,map_mul,Subgroup.coe_mul,seedARowSign_conjugate,seedACodeU_transport]
  rfl

noncomputable def hexadOriginalWord : SignedCoordinates SeedCoordinate :=
  seedPMonomial^6*seedWMonomial*seedAOriginalU 2
noncomputable def hexadCodeWord : codeGroup := codeP^6*codeW*seedACodeU 2

theorem hexadCodeWord_transport : hexadCodeWord.val=seedConjugateHom hexadOriginalWord := by
  simp only [hexadCodeWord,hexadOriginalWord,map_mul,map_pow,Subgroup.coe_mul,Subgroup.coe_pow,
    codeW_transport,seedACodeU_transport]
  rfl

noncomputable def secondFrameRaw (z : SeedCoordinate) : SeedCoordinate→ℤ :=
  secondFrameSign z.2 • seedOrbitOriginal (secondFrameOrbitIndex z)

theorem secondFrameInteger_raw (z : SeedCoordinate) :
    secondFrameInteger z=seedTransportLinear (secondFrameRaw z) := by
  rw [secondFrameInteger,seedOrbitWord,signedSeedTransport_eq_linear,secondFrameRaw,map_smul]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem hexad_integer_certificate :
    -secondFrameRaw (1,5)+secondFrameRaw (1,6)+secondFrameRaw (2,1)+secondFrameRaw (2,3)-
      secondFrameRaw (4,3)-secondFrameRaw (4,5)-
      (2 : ℤ) • liftedCoordinateHom hexadOriginalWord seedBArray=
      (8 : ℤ) • Pi.single (1,6) 1 := by
  decide +kernel

noncomputable def hexadGlueVector : RationalSpace := (1/2 : ℚ) •
  (-secondFrame (1,5)+secondFrame (1,6)+secondFrame (2,1)+secondFrame (2,3)-
    secondFrame (4,3)-secondFrame (4,5))

noncomputable def hexadEmbeddedDouble : IntegerCoordinates := seedTransportLinear
  ((4 : ℤ) • Pi.single (1,6) 1+liftedCoordinateHom hexadOriginalWord seedBArray)

theorem hexad_embedding_half : hexadGlueVector=halfCoordinates hexadEmbeddedDouble := by
  have h := congrArg (fun z : SeedCoordinate→ℤ => halfCoordinates (seedTransportLinear z)) hexad_integer_certificate
  simp only [map_add,map_sub,map_neg,map_smul] at h
  have hf (z : SeedCoordinate) : halfCoordinates (seedTransportLinear (secondFrameRaw z))=secondFrame z := by
    rw [←secondFrameInteger_raw]
    rfl
  simp only [hf] at h
  ext i
  have hi := congrFun h i
  change (1/2 : ℚ)*(-secondFrame (1,5) i+secondFrame (1,6) i+secondFrame (2,1) i+
    secondFrame (2,3) i-secondFrame (4,3) i-secondFrame (4,5) i)=_
  simp only [hexadEmbeddedDouble,map_add,map_smul] 
  norm_num at hi ⊢
  linarith

theorem doubledLattice_four_integer (z : IntegerCoordinates) : (4 : ℤ) • z∈doubledLattice := by
  have h : reduceModFour ((4 : ℤ) • z)=0 := by
    ext i
    change ((4*z i : ℤ) : ZMod 4)=0
    rw [Int.cast_mul]
    have h4 : ((4 : ℤ) : ZMod 4)=0 := by decide
    rw [h4,zero_mul]
  change reduceModFour ((4 : ℤ) • z)∈quaternaryCode
  rw [h]
  exact quaternaryCode.zero_mem

theorem integerMonomial_conjugate_transport (g : SignedCoordinates SeedCoordinate) (v : SeedCoordinate→ℤ) :
    integerMonomial (seedConjugateHom g) (signedSeedTransport v)=
      seedTransportLinear (liftedCoordinateHom g v) := by
  rw [signedSeedTransport_eq_linear]
  exact seedConjugate_lifted_transport g v

theorem hexad_action_integer :
    seedTransportLinear (liftedCoordinateHom hexadOriginalWord seedBArray)=
      integerMonomial hexadCodeWord.val (signedSeedTransport seedBArray) := by
  have h := integerMonomial_conjugate_transport hexadOriginalWord seedBArray
  rw [←hexadCodeWord_transport] at h
  exact h.symm

theorem hexadEmbeddedDouble_mem : hexadEmbeddedDouble∈doubledLattice := by
  rw [hexadEmbeddedDouble,map_add,map_smul,hexad_action_integer]
  apply doubledLattice.add_mem
  · exact doubledLattice_four_integer _
  · change reduceModFour (integerMonomial hexadCodeWord.val (signedSeedTransport seedBArray))∈quaternaryCode
    rw [integerMonomial_reduce]
    apply (hexadCodeWord.prop _).mp
    exact quaternaryCode_seed (0,0,0,1)

theorem hexadGlueVector_mem : hexadGlueVector∈rudvalisLattice := by
  rw [hexad_embedding_half]
  exact Submodule.mem_map_of_mem hexadEmbeddedDouble_mem

noncomputable def hexadUnsignedVector : RationalSpace := (1/2 : ℚ) •
  (secondFrame (1,5)+secondFrame (1,6)+secondFrame (2,1)+secondFrame (2,3)+
    secondFrame (4,3)+secondFrame (4,5))

theorem hexadUnsignedVector_eq : hexadUnsignedVector=
    hexadGlueVector+secondFrame (1,5)+secondFrame (4,3)+secondFrame (4,5) := by
  ext i
  change (1/2 : ℚ)*(secondFrame (1,5) i+secondFrame (1,6) i+secondFrame (2,1) i+
    secondFrame (2,3) i+secondFrame (4,3) i+secondFrame (4,5) i)=
    (1/2 : ℚ)*(-secondFrame (1,5) i+secondFrame (1,6) i+secondFrame (2,1) i+
    secondFrame (2,3) i-secondFrame (4,3) i-secondFrame (4,5) i)+
    secondFrame (1,5) i+secondFrame (4,3) i+secondFrame (4,5) i
  ring

theorem hexadUnsignedVector_mem : hexadUnsignedVector∈rudvalisLattice := by
  rw [hexadUnsignedVector_eq]
  exact rudvalisLattice.add_mem (rudvalisLattice.add_mem
    (rudvalisLattice.add_mem hexadGlueVector_mem (secondFrame_mem _)) (secondFrame_mem _))
    (secondFrame_mem _)

end Atlas.Rudvalis
