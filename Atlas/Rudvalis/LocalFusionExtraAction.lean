import Atlas.Rudvalis.LocalFusionExtraCertificate

set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

noncomputable def localExtraVector (n : Fin 9) (c : Fin 4) : RationalSpace :=
  seedIntegerRational (localExtraNumerator n c)

theorem localExtraVector_S (k : Fin 4) (c : Fin 4) :
    frameComparison (localExtraVector (![1,3,5,7] k) c)=
      (1/4:ℚ) • localExtraVector (![2,4,6,8] k) c :=
  frameComparison_integer_step _ _ (localExtraNumerator_S k c)

theorem localExtraVector_W (c : Fin 4) :
    rationalMonomialHom codeW.val (localExtraVector 0 c)=localExtraVector 1 c := by
  rw [codeW_transport]
  exact (rationalMonomial_conjugate_integer _ _).trans
    (congrArg seedIntegerRational (funext (localExtraNumerator_W c)))

theorem localExtraVector_V (c : Fin 4) :
    rationalMonomialHom codeV.val (localExtraVector 4 c)=localExtraVector 5 c := by
  rw [codeV_transport]
  exact (rationalMonomial_conjugate_integer _ _).trans
    (congrArg seedIntegerRational (funext (localExtraNumerator_V c)))

theorem localExtraVector_U (k : Fin 2) (c : Fin 4) :
    rationalMonomialHom codeU.val (localExtraVector (![2,6] k) c)=
      localExtraVector (![3,7] k) c := by
  have he : codeU.val=seedConjugateHom seedUMonomial := rfl
  rw [he]
  exact (rationalMonomial_conjugate_integer _ _).trans
    (congrArg seedIntegerRational (funext (localExtraNumerator_U k c)))

theorem localFusionT_extra_vectors (c : Fin 4) :
    localFusionT.val (localExtraVector 0 c)=(1/256:ℚ) • localExtraVector 8 c := by
  have hc (g : codeGroup) (v : RationalSpace) :
      (codeGaussianHom g).val v=rationalMonomialHom g.val v := rfl
  simp only [localFusionT,localFusionG,Subgroup.coe_mul,LinearEquiv.mul_apply,gaussianFrameExchange_val,hc]
  have hs1 : frameComparison (localExtraVector 1 c)=(1/4:ℚ) • localExtraVector 2 c := by
    simpa using localExtraVector_S 0 c
  have hs3 : frameComparison (localExtraVector 3 c)=(1/4:ℚ) • localExtraVector 4 c := by
    simpa using localExtraVector_S 1 c
  have hs5 : frameComparison (localExtraVector 5 c)=(1/4:ℚ) • localExtraVector 6 c := by
    simpa using localExtraVector_S 2 c
  have hs7 : frameComparison (localExtraVector 7 c)=(1/4:ℚ) • localExtraVector 8 c := by
    simpa using localExtraVector_S 3 c
  have hu2 : rationalMonomialHom codeU.val (localExtraVector 2 c)=localExtraVector 3 c := by
    simpa using localExtraVector_U 0 c
  have hu6 : rationalMonomialHom codeU.val (localExtraVector 6 c)=localExtraVector 7 c := by
    simpa using localExtraVector_U 1 c
  simp only [localExtraVector_W,hs1,hs3,hs5,hs7,hu2,hu6,localExtraVector_V,map_smul,smul_smul]
  norm_num


theorem localExtraVector_axis (c : Fin 4) (hc : c≠1) :
    localExtraVector 0 c=originalFrame (![(1,1),(0,0),(4,4),(1,2)] c) := by
  unfold localExtraVector seedIntegerRational originalFrame
  congr 1
  funext j
  simp [localExtraNumerator_zero,hc,Pi.single_apply]

theorem localExtraVector_seed : localExtraVector 0 1=seedIntegerRational seedP5Array := by
  apply congrArg seedIntegerRational
  funext j
  exact localExtraNumerator_zero 1 j

theorem seedIntegerRational_int_mul (a : ℤ) (v : SeedCoordinate→ℤ) :
    seedIntegerRational (fun j => a*v j)=(a:ℚ) • seedIntegerRational v := by
  unfold seedIntegerRational
  rw [←map_smul]
  congr 1
  funext j
  simp

theorem seedIntegerRational_axis (j : SeedCoordinate) :
    seedIntegerRational (fun i => if i=j then (2:ℤ) else 0)=originalFrame j := by
  unfold seedIntegerRational originalFrame
  congr 1
  funext i
  simp [Pi.single_apply]

theorem codeT_seedInteger (v : SeedCoordinate→ℤ) :
    (codeGaussianHom codeT).val (seedIntegerRational v)=
      seedIntegerRational (liftedCoordinateHom seedTMonomial v) :=
  rationalMonomial_conjugate_integer _ _

theorem codeI_seedInteger (v : SeedCoordinate→ℤ) :
    rationalI (seedIntegerRational v)=
      seedIntegerRational (liftedCoordinateHom (seedUnitMonomial 4) v) :=
  rationalMonomial_conjugate_integer _ _

noncomputable def localTripleTransport : gaussianLatticeGroup :=
  (codeGaussianHom codeT)^2*localFusionT

theorem localTripleTransport_extra (c : Fin 4) :
    localTripleTransport.val (localExtraVector 0 c)=
      (1/256:ℚ) • seedIntegerRational
        (liftedCoordinateHom seedTMonomial
          (liftedCoordinateHom seedTMonomial (localExtraNumerator 8 c))) := by
  simp only [localTripleTransport,pow_two,Subgroup.coe_mul,LinearEquiv.mul_apply]
  rw [localFusionT_extra_vectors]
  simp only [map_smul,localExtraVector,codeT_seedInteger]

theorem localTripleTransport_second :
    localTripleTransport.val (originalFrame (4,4))= -rationalI (originalFrame (0,2)) := by
  have h := localTripleTransport_extra 2
  rw [localExtraVector_axis 2 (by decide)] at h
  change localTripleTransport.val (originalFrame (4,4))=_ at h
  rw [h,funext localExtraNumerator_h_second,seedIntegerRational_int_mul,
    ←codeI_seedInteger,seedIntegerRational_axis,smul_smul]
  norm_num

noncomputable def shiftedSeedA : RationalSpace := (1/2:ℚ) • seedIntegerRational seedP5Array

theorem localTripleTransport_third :
    localTripleTransport.val (originalFrame (1,2))= -rationalI shiftedSeedA := by
  have h := localTripleTransport_extra 3
  rw [localExtraVector_axis 3 (by decide)] at h
  change localTripleTransport.val (originalFrame (1,2))=_ at h
  rw [h,funext localExtraNumerator_h_third,seedIntegerRational_int_mul,
    ←codeI_seedInteger,smul_smul]
  simp only [shiftedSeedA,map_smul]
  norm_num

theorem codeT_first_originalFrame :
    (codeGaussianHom codeT).val (originalFrame (0,1))=originalFrame (0,1) := by
  rw [←seedIntegerRational_axis,codeT_seedInteger]
  apply congrArg seedIntegerRational
  funext j
  decide +kernel +revert

theorem localTripleTransport_first :
    localTripleTransport.val (originalFrame (0,1))= -originalFrame (0,1) := by
  have h := localFusionT_columns 0
  change localFusionT.val (originalFrame (0,1))= -originalFrame (0,1) at h
  simp only [localTripleTransport,pow_two,Subgroup.coe_mul,LinearEquiv.mul_apply,
    h,map_neg,codeT_first_originalFrame]

theorem localTripleTransport_mem_generated : localTripleTransport∈generatedGaussianGroup :=
  generatedGaussianGroup.mul_mem
    (generatedGaussianGroup.pow_mem (codeGaussianHom_mem_generated codeT) 2)
    localFusionT_mem_generated

end Atlas.Rudvalis

