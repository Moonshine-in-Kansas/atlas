import Atlas.LinearGroups.ReeF4.RootSuzukiLeviBlocks
import Atlas.LinearGroups.ReeF4.SpecialIsotropyFormulas

/-! Concrete induced Suzuki tensor, in the retained negative natural4-block.
No restriction-image recognition is assumed. -/
noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def suzukiIntrinsicPolar (u v : Fin 4 → F) : F :=
  u 0*v 3+u 3*v 0+u 1*v 2+u 2*v 1

def suzukiIntrinsicRawTensor (u v : Fin 4 → F) : Fin 4 → F :=
  ![u 0*v 1+u 1*v 0,u 0*v 2+u 2*v 0,
    u 1*v 3+u 3*v 1,u 2*v 3+u 3*v 2]

theorem suzukiIntrinsicCoordinates_injective :
    Function.Injective (isotropyCoordinates (F := F)) :=
  Function.LeftInverse.injective isotropyPoint_coordinates

theorem suzukiIntrinsic_block1_coordinates (u : Fin 4 → F) :
    isotropyCoordinates (suzukiLeviBlockEmbed 1 u) =
      ![0,0,0,0,0,0,0,0,0,0,u 2,u 1,0,0,0,0,0,0,u 3,u 0,0,0,0,0,0,0] := by
  funext i
  fin_cases i <;>
    simp [isotropyCoordinates,suzukiLeviBlockEmbed,suzukiLeviBlockLabel,
      Fin.sum_univ_succ,rootVector,Pi.single_apply,smul_eq_mul,Fin.ext_iff]

theorem suzukiIntrinsic_block2_coordinates (u : Fin 4 → F) :
    isotropyCoordinates (suzukiLeviBlockEmbed 2 u) =
      ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,u 3,u 0,0,0,0,0,0,u 2,0,u 1,0,0] := by
  funext i
  fin_cases i <;>
    simp [isotropyCoordinates,suzukiLeviBlockEmbed,suzukiLeviBlockLabel,
      Fin.sum_univ_succ,rootVector,Pi.single_apply,smul_eq_mul,Fin.ext_iff]

theorem suzukiIntrinsic_block3_coordinates (u : Fin 4 → F) :
    isotropyCoordinates (suzukiLeviBlockEmbed 3 u) =
      ![0,0,0,0,0,0,0,0,0,0,0,0,u 3,u 0,0,0,0,0,0,0,u 2,0,u 1,0,0,0] := by
  funext i
  fin_cases i <;>
    simp [isotropyCoordinates,suzukiLeviBlockEmbed,suzukiLeviBlockLabel,
      Fin.sum_univ_succ,rootVector,Pi.single_apply,smul_eq_mul,Fin.ext_iff]

private theorem suzukiIntrinsic_root1_coordinates :
    isotropyCoordinates (rootVector (F := F) (0,1)) = ![0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  funext i
  fin_cases i <;> simp [isotropyCoordinates,rootVector,Pi.single_apply,Fin.ext_iff]

private theorem suzukiIntrinsic_root7_coordinates :
    isotropyCoordinates (rootVector (F := F) (0,7)) = ![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  funext i
  fin_cases i <;> simp [isotropyCoordinates,rootVector,Pi.single_apply,Fin.ext_iff]

theorem suzukiIntrinsic_cross_plus (u : Fin 4 → F) :
    traceZeroCross (rootVector (0,7)) (suzukiLeviBlockEmbed 1 u) =
      suzukiLeviBlockEmbed 2 u := by
  apply suzukiIntrinsicCoordinates_injective
  simp only [isotropyCross_actual,isotropyRawStar_actual,suzukiIntrinsic_block1_coordinates,suzukiIntrinsic_block2_coordinates]
  simp only [suzukiIntrinsic_root1_coordinates,suzukiIntrinsic_root7_coordinates]
  funext i
  fin_cases i <;>
    simp only [Fin.reduceFinMk,isotropyCross,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val,Pi.smul_apply,smul_eq_mul,
      suzukiIntrinsicPolar,zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero]
  all_goals ring

theorem suzukiIntrinsic_cross_minus3 (u : Fin 4 → F) :
    traceZeroCross (rootVector (0,1)) (suzukiLeviBlockEmbed 3 u) =
      suzukiLeviBlockEmbed 1 u := by
  apply suzukiIntrinsicCoordinates_injective
  simp only [isotropyCross_actual,isotropyRawStar_actual,suzukiIntrinsic_block3_coordinates,suzukiIntrinsic_block1_coordinates]
  simp only [suzukiIntrinsic_root1_coordinates,suzukiIntrinsic_root7_coordinates]
  funext i
  fin_cases i <;>
    simp only [Fin.reduceFinMk,isotropyCross,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val,Pi.smul_apply,smul_eq_mul,
      suzukiIntrinsicPolar,zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero]
  all_goals ring

theorem suzukiIntrinsic_mixed_cross (u v : Fin 4 → F) :
    traceZeroCross (suzukiLeviBlockEmbed 1 u) (suzukiLeviBlockEmbed 2 v) =
      suzukiIntrinsicPolar u v • rootVector (0,1) := by
  apply suzukiIntrinsicCoordinates_injective
  simp only [isotropyCross_actual,isotropyRawStar_actual,suzukiIntrinsic_block1_coordinates,suzukiIntrinsic_block2_coordinates,LinearMap.map_smul,Pi.smul_apply,smul_eq_mul]
  simp only [suzukiIntrinsic_root1_coordinates,suzukiIntrinsic_root7_coordinates]
  funext i
  fin_cases i <;>
    simp only [Fin.reduceFinMk,isotropyCross,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val,Pi.smul_apply,smul_eq_mul,
      suzukiIntrinsicPolar,zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero]
  all_goals ring

theorem suzukiIntrinsic_mixed_rawStar (u v : Fin 4 → F) :
    proposedStarLinear (wedge (suzukiLeviBlockEmbed 1 u) (suzukiLeviBlockEmbed 2 v)) =
      suzukiLeviBlockEmbed 3 (suzukiIntrinsicRawTensor u v) := by
  apply suzukiIntrinsicCoordinates_injective
  simp only [isotropyCross_actual,isotropyRawStar_actual,suzukiIntrinsic_block1_coordinates,suzukiIntrinsic_block2_coordinates,suzukiIntrinsic_block3_coordinates]
  funext i
  fin_cases i <;>
    simp [isotropyCross,isotropyRawStar,isotropyCoordinates,rootVector,
      Pi.single_apply,suzukiIntrinsicPolar,suzukiIntrinsicRawTensor,Fin.ext_iff]
  all_goals ring

theorem suzukiIntrinsic_mixed_polar (u v : Fin 4 → F) :
    traceZeroPolar (suzukiLeviBlockEmbed 1 u) (suzukiLeviBlockEmbed 2 v) = 0 := by
  rw [isotropyPolar_actual,suzukiIntrinsic_block1_coordinates,suzukiIntrinsic_block2_coordinates]
  simp [isotropyPolar]

theorem suzukiIntrinsic_mixed_domain (u v : Fin 4 → F)
    (h : suzukiIntrinsicPolar u v = 0) :
    StarDomain (suzukiLeviBlockEmbed 1 u) (suzukiLeviBlockEmbed 2 v) := by
  constructor
  · exact suzukiIntrinsic_mixed_polar u v
  · rw [suzukiIntrinsic_mixed_cross,h,zero_smul]

theorem suzukiIntrinsic_map_block3 (σ : F →+* F) (u : Fin 4 → F) :
    traceZeroMap σ (suzukiLeviBlockEmbed 3 u) =
      suzukiLeviBlockEmbed 3 (fun i => σ (u i)) := by
  have hmap (w : TraceZero F) : isotropyCoordinates (traceZeroMap σ w) =
      fun i => σ (isotropyCoordinates w i) := by
    funext i
    fin_cases i <;> rfl
  apply suzukiIntrinsicCoordinates_injective
  rw [hmap,suzukiIntrinsic_block3_coordinates,suzukiIntrinsic_block3_coordinates]
  funext i
  fin_cases i <;> simp

/-- The partial W4 tensor is recovered intrinsically, not from an ovoid set. -/
theorem suzukiIntrinsic_tensor_actual (σ : F →+* F) (u v : Fin 4 → F)
    (h : suzukiIntrinsicPolar u v = 0) :
    traceZeroCross (rootVector (0,1))
      (proposedPartialProduct σ (suzukiLeviBlockEmbed 1 u) (suzukiLeviBlockEmbed 2 v)
        (suzukiIntrinsic_mixed_domain u v h)) =
      suzukiLeviBlockEmbed 1 (fun i => σ (suzukiIntrinsicRawTensor u v i)) := by
  change traceZeroCross (rootVector (0,1))
    (traceZeroMap σ (proposedStarLinear
      (wedge (suzukiLeviBlockEmbed 1 u) (suzukiLeviBlockEmbed 2 v)))) = _
  rw [suzukiIntrinsic_mixed_rawStar,suzukiIntrinsic_map_block3,
    suzukiIntrinsic_cross_minus3]

end Atlas.ReeF4
