import Atlas.LinearGroups.ReeF4.SpecialIsotropyFormulas
import Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows
import Atlas.LinearGroups.ReeF4.RootSuzukiLeviBlocks
import Atlas.LinearGroups.ReeF4.PartialCandidate

/-! An intrinsic image construction for the negative
Suzuki four-space. No ovoid recognition or group-order input is used. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [CharP F 2]

private theorem oppositeImage_coordinates_injective :
    Function.Injective (isotropyCoordinates (F := F)) := by
  intro u v h
  simpa only [isotropyPoint_coordinates] using congrArg isotropyPoint h

private def imageE : Fin 26 → F :=
  ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def imageD : Fin 26 → F :=
  ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def imageBlock (v : Fin 4 → F) : Fin 26 → F :=
  ![0,0,0,0,0,0,0,0,0,0,v 2,v 1,0,0,0,0,0,0,v 3,v 0,0,0,0,0,0,0]
private def imagePre (v : Fin 4 → F) : Fin 26 → F :=
  ![0,0,0,0,v 3,v 2,v 1,v 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

private theorem imageE_actual : isotropyCoordinates (rootVector (F := F) (0,0))=imageE := by
  funext i
  fin_cases i <;> simp [imageE,isotropyCoordinates,rootVector,Pi.single_apply,Fin.ext_iff]
private theorem imageD_actual : isotropyCoordinates (diagonalVector (F := F) 0)=imageD := by
  funext i
  fin_cases i <;> simp [imageD,isotropyCoordinates,diagonalVector,traceZeroProjection,trace,unit,CharTwo.neg_eq,Pi.single_apply,Fin.ext_iff]
private theorem imageBlock_actual (v : Fin 4 → F) :
    isotropyCoordinates (suzukiLeviBlockEmbed 1 v)=imageBlock v := by
  funext i
  fin_cases i <;> simp [imageBlock,isotropyCoordinates,suzukiLeviBlockEmbed,
    suzukiLeviBlockLabel,Fin.sum_univ_succ,rootVector,Pi.single_apply,Fin.ext_iff]
private theorem imagePoint_coordinates (x : Fin 26 → F) :
    isotropyCoordinates (isotropyPoint x)=x := by
  funext i
  fin_cases i <;> rfl
private theorem imagePartial_coordinates (σ : F →+* F) (u v : TraceZero F)
    (hd : StarDomain u v) :
    isotropyCoordinates (proposedPartialProduct σ u v hd)=
      fun i => σ (isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) i) := by
  change isotropyCoordinates (traceZeroMap σ (proposedStarLinear (wedge u v)))=_
  rw [isotropyCoordinates_map,isotropyRawStar_actual]

private theorem image_raw_formula (σ : F →+* F) (x : Fin 26 → F) :
    isotropyCross imageD (fun i => σ (isotropyRawStar imageE x i))=
      imageBlock ![σ (x 7),σ (x 6),σ (x 5),σ (x 4)] := by
  funext i
  fin_cases i <;>
    simp only [isotropyCross_row0,isotropyCross_row1,isotropyCross_row2,isotropyCross_row3,isotropyCross_row4,isotropyCross_row5,isotropyCross_row6,isotropyCross_row7,isotropyCross_row8,isotropyCross_row9,isotropyCross_row10,isotropyCross_row11,isotropyCross_row12,isotropyCross_row13,isotropyCross_row14,isotropyCross_row15,isotropyCross_row16,isotropyCross_row17,isotropyCross_row18,isotropyCross_row19,isotropyCross_row20,isotropyCross_row21,isotropyCross_row22,isotropyCross_row23,isotropyCross_row24,isotropyCross_row25,isotropyRawStar_row0,isotropyRawStar_row1,isotropyRawStar_row2,isotropyRawStar_row3,isotropyRawStar_row4,isotropyRawStar_row5,isotropyRawStar_row6,isotropyRawStar_row7,isotropyRawStar_row8,isotropyRawStar_row9,isotropyRawStar_row10,isotropyRawStar_row11,isotropyRawStar_row12,isotropyRawStar_row13,isotropyRawStar_row14,isotropyRawStar_row15,isotropyRawStar_row16,isotropyRawStar_row17,isotropyRawStar_row18,isotropyRawStar_row19,isotropyRawStar_row20,isotropyRawStar_row21,isotropyRawStar_row22,isotropyRawStar_row23,isotropyRawStar_row24,isotropyRawStar_row25,imageD,imageE,imageBlock,Fin.reduceFinMk,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero,Pi.zero_apply,map_zero,map_one]

private theorem image_pre_polar (v : Fin 4 → F) :
    isotropyPolar imageE (imagePre v)=0 := by
  simp [isotropyPolar,imageE,imagePre]
private theorem image_pre_cross (v : Fin 4 → F) :
    isotropyCross imageE (imagePre v)=0 := by
  funext i
  fin_cases i <;> simp only [isotropyCross_row0,isotropyCross_row1,isotropyCross_row2,isotropyCross_row3,isotropyCross_row4,isotropyCross_row5,isotropyCross_row6,isotropyCross_row7,isotropyCross_row8,isotropyCross_row9,isotropyCross_row10,isotropyCross_row11,isotropyCross_row12,isotropyCross_row13,isotropyCross_row14,isotropyCross_row15,isotropyCross_row16,isotropyCross_row17,isotropyCross_row18,isotropyCross_row19,isotropyCross_row20,isotropyCross_row21,isotropyCross_row22,isotropyCross_row23,isotropyCross_row24,isotropyCross_row25,imageE,imagePre,Fin.reduceFinMk,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero,Pi.zero_apply]

/-- The intrinsic image is already supported on the four natural coordinates.
The hypothesis is necessary to interpret the actual partial product. -/
theorem oppositePairImage_formula (σ : F →+* F) (w : TraceZero F)
    (hd : StarDomain (rootVector (0,0)) w) :
    traceZeroCross (diagonalVector 0)
      (proposedPartialProduct σ (rootVector (0,0)) w hd) =
    suzukiLeviBlockEmbed 1
      ![σ (w.val.2 0 5),σ (w.val.2 0 4),σ (w.val.2 0 3),σ (w.val.2 0 2)] := by
  apply oppositeImage_coordinates_injective
  rw [isotropyCross_actual,imagePartial_coordinates,imageD_actual,imageE_actual,
    imageBlock_actual]
  exact image_raw_formula σ (isotropyCoordinates w)

/-- An explicit preimage, before applying the inverse Tits map. -/
def oppositePairImagePreimage (σ : F ≃+* F) (v : Fin 4 → F) : TraceZero F :=
  isotropyPoint (imagePre (fun i => σ.symm (v i)))

theorem oppositePairImagePreimage_domain (σ : F ≃+* F) (v : Fin 4 → F) :
    StarDomain (rootVector (0,0)) (oppositePairImagePreimage σ v) := by
  have hc : isotropyCoordinates (oppositePairImagePreimage σ v)=
      imagePre (fun i => σ.symm (v i)) :=
    imagePoint_coordinates _
  constructor
  · rw [isotropyPolar_actual,imageE_actual,hc,image_pre_polar]
  · apply oppositeImage_coordinates_injective
    rw [isotropyCross_actual,imageE_actual,hc,image_pre_cross,map_zero]

theorem oppositePairImagePreimage_image (σ : F ≃+* F) (v : Fin 4 → F) :
    traceZeroCross (diagonalVector 0)
      (proposedPartialProduct σ.toRingHom (rootVector (0,0))
        (oppositePairImagePreimage σ v) (oppositePairImagePreimage_domain σ v)) =
      suzukiLeviBlockEmbed 1 v := by
  rw [oppositePairImage_formula]
  congr 1
  funext i
  fin_cases i <;> simp [oppositePairImagePreimage,isotropyPoint,imagePre]

/-- Exact intrinsic characterization of the natural four-space. -/
theorem mem_negativeSuzukiBlock_iff_intrinsicImage (σ : F ≃+* F) (z : TraceZero F) :
    z ∈ LinearMap.range (suzukiLeviBlockEmbed (F := F) 1) ↔
      ∃ w : TraceZero F, ∃ hd : StarDomain (rootVector (0,0)) w,
        traceZeroCross (diagonalVector 0)
          (proposedPartialProduct σ.toRingHom (rootVector (0,0)) w hd) = z := by
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨oppositePairImagePreimage σ v,oppositePairImagePreimage_domain σ v,
      oppositePairImagePreimage_image σ v⟩
  · rintro ⟨w,hd,rfl⟩
    rw [oppositePairImage_formula]
    exact ⟨_,rfl⟩
end Atlas.ReeF4
