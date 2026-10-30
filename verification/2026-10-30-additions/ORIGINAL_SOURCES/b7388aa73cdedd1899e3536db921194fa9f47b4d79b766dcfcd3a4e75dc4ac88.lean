import Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

private theorem suzukiIntrinsic_firstRoot_coordinates :
    isotropyCoordinates (rootVector (F := F) (0,0)) =
      ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  funext i
  fin_cases i <;> simp [isotropyCoordinates,rootVector,Pi.single_apply,Fin.ext_iff]

theorem suzukiIntrinsic_same_cross (u v : Fin 4 → F) :
    traceZeroCross (suzukiLeviBlockEmbed 1 u) (suzukiLeviBlockEmbed 1 v)=0 := by
  apply suzukiIntrinsicCoordinates_injective
  simp only [isotropyCross_actual,suzukiIntrinsic_block1_coordinates,_root_.map_zero]
  funext i
  fin_cases i <;>
    simp only [isotropyCross,Matrix.cons_val,Fin.reduceFinMk,Matrix.cons_val_zero,Matrix.cons_val_succ,Pi.zero_apply,
      zero_mul,mul_zero,zero_add,add_zero]

theorem suzukiIntrinsic_same_polar (u v : Fin 4 → F) :
    traceZeroPolar (suzukiLeviBlockEmbed 1 u) (suzukiLeviBlockEmbed 1 v)=0 := by
  rw [isotropyPolar_actual,suzukiIntrinsic_block1_coordinates,suzukiIntrinsic_block1_coordinates]
  simp only [isotropyPolar,Matrix.cons_val,Fin.reduceFinMk,Matrix.cons_val_zero,Matrix.cons_val_succ,zero_mul,mul_zero,zero_add,add_zero]

theorem suzukiIntrinsic_same_domain (u v : Fin 4 → F) :
    StarDomain (suzukiLeviBlockEmbed 1 u) (suzukiLeviBlockEmbed 1 v) :=
  ⟨suzukiIntrinsic_same_polar u v,suzukiIntrinsic_same_cross u v⟩

theorem suzukiIntrinsic_same_rawStar (u v : Fin 4 → F) :
    proposedStarLinear (wedge (suzukiLeviBlockEmbed 1 u) (suzukiLeviBlockEmbed 1 v)) =
      suzukiIntrinsicPolar u v • rootVector (0,0) := by
  apply suzukiIntrinsicCoordinates_injective
  simp only [isotropyRawStar_actual,suzukiIntrinsic_block1_coordinates,LinearMap.map_smul,
    suzukiIntrinsic_firstRoot_coordinates]
  funext i
  fin_cases i <;>
    simp only [isotropyRawStar,Matrix.cons_val,Fin.reduceFinMk,Matrix.cons_val_zero,Matrix.cons_val_succ,Pi.smul_apply,smul_eq_mul,
      suzukiIntrinsicPolar,zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero]
  all_goals ring

theorem suzukiIntrinsic_map_firstRoot_smul (σ : F →+* F) (a : F) :
    traceZeroMap σ (a • rootVector (0,0)) = σ a • rootVector (0,0) := by
  apply suzukiIntrinsicCoordinates_injective
  rw [isotropyCoordinates_map]
  simp only [LinearMap.map_smul,suzukiIntrinsic_firstRoot_coordinates]
  funext i
  fin_cases i <;>
    simp only [Matrix.cons_val,Fin.reduceFinMk,Matrix.cons_val_zero,Matrix.cons_val_succ,Pi.smul_apply,smul_eq_mul,mul_zero,mul_one,map_zero]

theorem suzukiIntrinsic_same_partial (σ : F →+* F) (u v : Fin 4 → F) :
    proposedPartialProduct σ (suzukiLeviBlockEmbed 1 u) (suzukiLeviBlockEmbed 1 v)
      (suzukiIntrinsic_same_domain u v) = σ (suzukiIntrinsicPolar u v) • rootVector (0,0) := by
  change traceZeroMap σ (proposedStarLinear
    (wedge (suzukiLeviBlockEmbed 1 u) (suzukiLeviBlockEmbed 1 v))) = _
  rw [suzukiIntrinsic_same_rawStar,suzukiIntrinsic_map_firstRoot_smul]

end Atlas.ReeF4
