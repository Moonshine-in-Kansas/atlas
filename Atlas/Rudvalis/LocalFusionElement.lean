import Atlas.Rudvalis.LocalFusionCertificate
import Atlas.Rudvalis.GaussianFrameExchangeAction
import Atlas.Rudvalis.CoordinateCrossOrthogonality

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators

noncomputable def localFusionG : gaussianLatticeGroup :=
  gaussianFrameExchange*codeGaussianHom codeU*gaussianFrameExchange
noncomputable def localFusionT : gaussianLatticeGroup :=
  localFusionG*codeGaussianHom codeV*localFusionG*codeGaussianHom codeW

theorem localFusionG_mem_generated : localFusionG∈generatedGaussianGroup :=
  generatedGaussianGroup.mul_mem
    (generatedGaussianGroup.mul_mem gaussianFrameExchange_mem_generated (codeGaussianHom_mem_generated _))
    gaussianFrameExchange_mem_generated

theorem localFusionT_mem_generated : localFusionT∈generatedGaussianGroup :=
  generatedGaussianGroup.mul_mem
    (generatedGaussianGroup.mul_mem
      (generatedGaussianGroup.mul_mem localFusionG_mem_generated (codeGaussianHom_mem_generated _))
      localFusionG_mem_generated) (codeGaussianHom_mem_generated _)

theorem frameComparison_integer_step (a b : SeedCoordinate→ℤ)
    (h : ∀j,b j=∑i,frameComparisonRaw i j*a i) :
    frameComparison (seedIntegerRational a)=(1/4:ℚ) • seedIntegerRational b := by
  apply seedTransportLinear.symm.injective
  funext j
  rw [frameComparison_raw_formula]
  simp only [seedIntegerRational,LinearEquiv.symm_apply_apply,map_smul,Pi.smul_apply,smul_eq_mul]
  rw [h]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

noncomputable def localFusionVector (n : Fin 9) (c : Fin 3) : RationalSpace :=
  seedIntegerRational (localFusionNumerator n c)

theorem localFusionVector_zero (c : Fin 3) :
    localFusionVector 0 c=originalFrame (localFusionSource c) := by
  unfold localFusionVector seedIntegerRational originalFrame
  congr 1
  funext j
  simp [localFusionNumerator_zero,Pi.single_apply]

theorem localFusionVector_final (c : Fin 3) :
    localFusionVector 8 c=(-256:ℚ) • originalFrame (localFusionTarget c) := by
  unfold localFusionVector seedIntegerRational originalFrame
  rw [←map_smul]
  congr 1
  funext j
  simp [localFusionNumerator_final,Pi.single_apply]
  split_ifs <;> norm_num

theorem localFusionVector_S (k : Fin 4) (c : Fin 3) :
    frameComparison (localFusionVector (![1,3,5,7] k) c)=
      (1/4:ℚ) • localFusionVector (![2,4,6,8] k) c :=
  frameComparison_integer_step _ _ (localFusionNumerator_S k c)

theorem localFusionVector_W (c : Fin 3) :
    rationalMonomialHom codeW.val (localFusionVector 0 c)=localFusionVector 1 c := by
  rw [codeW_transport]
  exact (rationalMonomial_conjugate_integer _ _).trans
    (congrArg seedIntegerRational (funext (localFusionNumerator_W c)))

theorem localFusionVector_V (c : Fin 3) :
    rationalMonomialHom codeV.val (localFusionVector 4 c)=localFusionVector 5 c := by
  rw [codeV_transport]
  exact (rationalMonomial_conjugate_integer _ _).trans
    (congrArg seedIntegerRational (funext (localFusionNumerator_V c)))

theorem localFusionVector_U (k : Fin 2) (c : Fin 3) :
    rationalMonomialHom codeU.val (localFusionVector (![2,6] k) c)=
      localFusionVector (![3,7] k) c := by
  have he : codeU.val=seedConjugateHom seedUMonomial := rfl
  rw [he]
  exact (rationalMonomial_conjugate_integer _ _).trans
    (congrArg seedIntegerRational (funext (localFusionNumerator_U k c)))

theorem localFusionT_columns (c : Fin 3) :
    localFusionT.val (originalFrame (localFusionSource c))= -originalFrame (localFusionTarget c) := by
  have hc (g : codeGroup) (v : RationalSpace) :
      (codeGaussianHom g).val v=rationalMonomialHom g.val v := rfl
  simp only [localFusionT,localFusionG,Subgroup.coe_mul,LinearEquiv.mul_apply,gaussianFrameExchange_val,hc]
  have hs1 : frameComparison (localFusionVector 1 c)=(1/4:ℚ) • localFusionVector 2 c := by
    simpa using localFusionVector_S 0 c
  have hs3 : frameComparison (localFusionVector 3 c)=(1/4:ℚ) • localFusionVector 4 c := by
    simpa using localFusionVector_S 1 c
  have hs5 : frameComparison (localFusionVector 5 c)=(1/4:ℚ) • localFusionVector 6 c := by
    simpa using localFusionVector_S 2 c
  have hs7 : frameComparison (localFusionVector 7 c)=(1/4:ℚ) • localFusionVector 8 c := by
    simpa using localFusionVector_S 3 c
  have hu2 : rationalMonomialHom codeU.val (localFusionVector 2 c)=localFusionVector 3 c := by
    simpa using localFusionVector_U 0 c
  have hu6 : rationalMonomialHom codeU.val (localFusionVector 6 c)=localFusionVector 7 c := by
    simpa using localFusionVector_U 1 c
  rw [←localFusionVector_zero]
  simp only [localFusionVector_W,hs1,hs3,hs5,hs7,hu2,hu6,localFusionVector_V,map_smul,
    localFusionVector_final,smul_smul]
  norm_num

end Atlas.Rudvalis
