import Atlas.Tits.OddRelationMatrices
import Atlas.Tits.OriginalMatrixRepresentation
import Atlas.Tits.NormalIndexReduction

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary

noncomputable def rationalSeedMatrix : RealSeedMatrix →+*
    Matrix SeedCoordinate SeedCoordinate ℚ := (Int.castRingHom ℚ).mapMatrix

theorem rationalSeedMatrix_smul (a : ℤ) (M : RealSeedMatrix) :
    rationalSeedMatrix (a • M) = (a:ℚ) • rationalSeedMatrix M := by
  ext i j
  change ((a * M i j : ℤ):ℚ) = (a:ℚ) * (M i j:ℚ)
  exact Int.cast_mul _ _

theorem originalMatrix_U : originalGroupMatrix (codeGaussianHom codeU) =
    rationalSeedMatrix (originalMonomialMatrix seedUMonomial) :=
  originalMatrix_monomial codeU seedUMonomial rfl

theorem originalMatrix_G : originalGroupMatrix localFusionG =
    (1/4:ℚ) • rationalSeedMatrix fusionGMatrix := by
  have hs : originalGroupMatrix gaussianFrameExchange =
      (1/4:ℚ) • rationalSeedMatrix frameIntegerMatrix := originalMatrix_frame
  rw [localFusionG,map_mul,map_mul,hs,originalMatrix_U]
  calc
    _ = (1/16:ℚ) • rationalSeedMatrix
        (frameIntegerMatrix * (originalMonomialMatrix seedUMonomial * frameIntegerMatrix)) := by
      rw [map_mul,map_mul]
      simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.mul_assoc]
      norm_num
    _ = _ := by
      rw [fusionUSMatrix_certificate,fusionGMatrix_certificate,rationalSeedMatrix_smul,smul_smul]
      norm_num

noncomputable def oddSecondCode : codeGroup := codeR * seedARowSign (binaryLabel 3) * codeU

theorem oddSecondCode_transport : oddSecondCode.val = seedConjugateHom oddSecondMonomial := by
  simp only [oddSecondCode,oddSecondMonomial,Subgroup.coe_mul,map_mul,seedARowSign_conjugate]
  rfl

theorem originalMatrix_oddFirst : originalGroupMatrix (localFusionG * codeGaussianHom codeU) =
    (1/4:ℚ) • rationalSeedMatrix oddFirstMatrix := by
  rw [map_mul,originalMatrix_G,originalMatrix_U,Matrix.smul_mul,←map_mul,oddFirstMatrix_certificate]

theorem originalMatrix_oddSecond : originalGroupMatrix (codeGaussianHom oddSecondCode * localFusionG) =
    (1/4:ℚ) • rationalSeedMatrix oddSecondMatrix := by
  rw [map_mul,originalMatrix_monomial oddSecondCode oddSecondMonomial oddSecondCode_transport,
    originalMatrix_G]
  change rationalSeedMatrix (originalMonomialMatrix oddSecondMonomial) * _ = _
  rw [Matrix.mul_smul,←map_mul,oddSecondMatrix_certificate]

theorem scaled_matrix_cube (A B : RealSeedMatrix) (c : ℤ)
    (h2 : A*A=B) (h3 : B*A=c • (1:RealSeedMatrix)) :
    ((1/4:ℚ) • rationalSeedMatrix A)^3 = (c/64:ℚ) • (1:Matrix SeedCoordinate SeedCoordinate ℚ) := by
  rw [show (3:ℕ)=2+1 from rfl,pow_succ,pow_two]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [←map_mul,h2,←map_mul,h3,rationalSeedMatrix_smul,map_one,smul_smul]
  congr 1
  ring

theorem gaussian_odd_first : (localFusionG * codeGaussianHom codeU)^3 = 1 := by
  apply originalGroupMatrix_injective
  rw [map_pow,originalMatrix_oddFirst,map_one,
    scaled_matrix_cube _ _ 64 oddFirstSquare_certificate oddFirstCube_certificate]
  norm_num

theorem originalMatrix_negative_scalar :
    originalGroupMatrix (codeGaussianHom (codeI^2)) = -(1:Matrix SeedCoordinate SeedCoordinate ℚ) := by
  have he : (codeGaussianHom (codeI^2)).val.toLinearMap = -(1:Module.End ℚ RationalSpace) := by
    apply LinearMap.ext
    intro v
    funext i
    change rationalMonomialHom (codeI^2).val v i = -v i
    rw [pow_two,Subgroup.coe_mul,codeI_squared_signed,negativeMonomial_rational]
    rfl
  change originalMatrix _ = _
  rw [he,map_neg,map_one]

theorem gaussian_odd_second :
    (codeGaussianHom oddSecondCode * localFusionG)^3 = codeGaussianHom (codeI^2) := by
  apply originalGroupMatrix_injective
  rw [map_pow,originalMatrix_oddSecond,originalMatrix_negative_scalar,
    scaled_matrix_cube _ _ (-64) oddSecondSquare_certificate oddSecondCube_certificate]
  norm_num

theorem localGU_cube : (localG * codePointHom pointU)^3 = 1 := by
  apply Subtype.ext
  change QuotientGroup.mk ((localFusionG * codeGaussianHom codeU)^3) = _
  rw [gaussian_odd_first]
  rfl

theorem localREUg_cube :
    (codePointHom pointR * codePointHom pointE3 * codePointHom pointU * localG)^3 = 1 := by
  apply Subtype.ext
  change QuotientGroup.mk
    ((codeGaussianHom codeR * codeGaussianHom (seedARowSign (binaryLabel 3)) *
      codeGaussianHom codeU * localFusionG)^3) = _
  rw [←map_mul,←map_mul]
  change QuotientGroup.mk ((codeGaussianHom oddSecondCode * localFusionG)^3) = _
  rw [gaussian_odd_second]
  change codeToRudvalis (codeI^2) = 1
  rw [map_pow,codeToRudvalis_I,one_pow]

theorem normal_index_le_two (N : Subgroup Ambient) [N.Normal] (hN : N ≠ ⊥) : N.index ≤ 2 :=
  normal_index_le_two_of_odd_relations localGU_cube localREUg_cube N hN

end Atlas.Tits
