import Atlas.Rudvalis.LocalFusionExtraAction

namespace Atlas.Rudvalis
open scoped BigOperators

noncomputable def originalRowEnergy (r : Fin 7) (v : RationalSpace) : ℚ :=
  ∑k : Fin 8,(seedTransportLinear.symm v (r,k))^2

theorem originalRowEnergy_smul (r : Fin 7) (a : ℚ) (v : RationalSpace) :
    originalRowEnergy r (a • v)=a^2*originalRowEnergy r v := by
  simp only [originalRowEnergy,map_smul,Pi.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]

theorem originalRowEnergy_seedInteger (r : Fin 7) (v : SeedCoordinate→ℤ) :
    originalRowEnergy r (seedIntegerRational v)=((∑k : Fin 8,v (r,k)^2 : ℤ):ℚ) := by
  simp only [originalRowEnergy,seedIntegerRational,LinearEquiv.symm_apply_apply,Int.cast_sum,Int.cast_pow]

theorem localExtraVector_final_rowEnergy (c : Fin 2) (r : Fin 7) :
    originalRowEnergy r (localExtraVector 8 c.castSucc.castSucc)=
      (65536:ℚ)*(![![0,1,1,1,0,0,1],![2,2,2,2,2,4,2]] c r) := by
  rw [localExtraVector,originalRowEnergy_seedInteger,localExtraNumerator_energy]
  push_cast
  fin_cases c <;> fin_cases r <;> norm_num

theorem localFusionT_coordinate_bridge_energy (r : Fin 7) :
    originalRowEnergy r (localFusionT.val (originalFrame (1,1)))=
      ![0,1,1,1,0,0,1] r := by
  have hi := localExtraVector_axis 0 (by decide)
  change localExtraVector 0 0=originalFrame (1,1) at hi
  rw [←hi,localFusionT_extra_vectors,originalRowEnergy_smul]
  have he := localExtraVector_final_rowEnergy 0 r
  change originalRowEnergy r (localExtraVector 8 0)=65536*(![0,1,1,1,0,0,1] r) at he
  rw [he]
  ring

theorem localFusionT_seed_bridge_energy (r : Fin 7) :
    originalRowEnergy r (localFusionT.val shiftedSeedA)=
      ![1/2,1/2,1/2,1/2,1/2,1,1/2] r := by
  rw [shiftedSeedA,←localExtraVector_seed,map_smul,localFusionT_extra_vectors,
    originalRowEnergy_smul,originalRowEnergy_smul]
  have he := localExtraVector_final_rowEnergy 1 r
  change originalRowEnergy r (localExtraVector 8 1)=65536*(![2,2,2,2,2,4,2] r) at he
  rw [he]
  fin_cases r <;> norm_num

end Atlas.Rudvalis
