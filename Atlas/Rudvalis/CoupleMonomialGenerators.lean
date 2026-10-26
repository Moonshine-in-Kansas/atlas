import Atlas.Rudvalis.LocalFusionAction
import Atlas.Rudvalis.FourLocalWords

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

noncomputable def coupleCodeD : codeGroup := (codeP^2)⁻¹*codeR*codeP
noncomputable def coupleCodeBeta : codeGroup := coupleCodeD⁻¹*codeR*coupleCodeD^2
noncomputable def coupleOriginalD : SignedCoordinates SeedCoordinate :=
  (seedPMonomial^2)⁻¹*seedRMonomial*seedPMonomial
noncomputable def coupleOriginalBeta : SignedCoordinates SeedCoordinate :=
  coupleOriginalD⁻¹*seedRMonomial*coupleOriginalD^2

theorem coupleCodeD_transport : coupleCodeD.val=seedConjugateHom coupleOriginalD := by
  simp only [coupleCodeD,coupleOriginalD,map_mul,map_pow,map_inv,Subgroup.coe_mul,
    Subgroup.coe_pow,Subgroup.coe_inv]
  rfl

theorem coupleCodeBeta_transport : coupleCodeBeta.val=seedConjugateHom coupleOriginalBeta := by
  simp only [coupleCodeBeta,coupleOriginalBeta,map_mul,map_pow,map_inv,Subgroup.coe_mul,
    Subgroup.coe_pow,Subgroup.coe_inv,coupleCodeD_transport]
  rfl

def coupleBetaRow (r : Fin 7) : Fin 7 := ![0,6,1,2,5,4,3] r

theorem coupleOriginalBeta_row (r : Fin 7) (k : Fin 8) :
    (coupleOriginalBeta.right (r,k)).1=coupleBetaRow r := by decide +kernel +revert

theorem coupleOriginalR_row (r : Fin 7) (k : Fin 8) :
    (seedRMonomial.right (r,k)).1=seedRRow r := rfl

theorem coupleOriginal_fixed_coordinates :
    seedRMonomial.right (0,1)=(0,1) ∧ seedRMonomial.right (0,2)=(0,2) ∧
    (coupleOriginalBeta.right (0,1)=(0,1) ∨ coupleOriginalBeta.right (0,1)=(0,0)) ∧
    (coupleOriginalBeta.right (0,2)=(0,2) ∨ coupleOriginalBeta.right (0,2)=(0,3)) := by
  decide +kernel

theorem originalCoordinateEquiv_row (z : SeedCoordinate) :
    (originalCoordinateEquiv z).1=rowLabel z.1 := rfl

theorem coupleCodeBeta_row (r : Fin 7) (k : Fin 8) :
    (coupleCodeBeta.val.right (originalCoordinateEquiv (r,k))).1=rowLabel (coupleBetaRow r) := by
  rw [coupleCodeBeta_transport]
  change ((seedConjugateMonomial coupleOriginalBeta).right (originalCoordinateEquiv (r,k))).1=_
  rw [seedConjugateMonomial_right,original_congr_apply]
  rw [originalCoordinateEquiv_row,coupleOriginalBeta_row]

theorem coupleCodeR_row (r : Fin 7) (k : Fin 8) :
    (codeR.val.right (originalCoordinateEquiv (r,k))).1=rowLabel (seedRRow r) := by
  rw [codeR_right,original_congr_apply]
  rfl

theorem original_second_coordinate_cross_fix (g : codeGroup) (h : SignedCoordinates SeedCoordinate)
    (hg : g.val=seedConjugateHom h)
    (hh : h.right (0,2)=(0,2) ∨ h.right (0,2)=(0,3)) :
    g • coordinateCross (originalCoordinateEquiv (0,2))=coordinateCross (originalCoordinateEquiv (0,2)) := by
  rw [coordinateCross_action,hg]
  change coordinateCross ((seedConjugateMonomial h).right (originalCoordinateEquiv (0,2)))=_
  rw [seedConjugateMonomial_right,original_congr_apply]
  rcases hh with hh|hh
  · rw [hh]
  · rw [hh]
    have hi : codeI.val.right (originalCoordinateEquiv (0,2))=originalCoordinateEquiv (0,3) := by
      rw [codeI_coordinate]
      decide +kernel
    rw [←hi,coordinateCross_I]

theorem coupleCodeR_fixes_reference :
    codeR • coordinateCross (localFusionSourceCoordinate 0)=coordinateCross (localFusionSourceCoordinate 0) ∧
    codeR • coordinateCross (localFusionSourceCoordinate 1)=coordinateCross (localFusionSourceCoordinate 1) := by
  exact ⟨original_coordinate_cross_fix codeR seedRMonomial rfl (Or.inl coupleOriginal_fixed_coordinates.1),
    original_second_coordinate_cross_fix codeR seedRMonomial rfl (Or.inl coupleOriginal_fixed_coordinates.2.1)⟩

theorem coupleCodeBeta_fixes_reference :
    coupleCodeBeta • coordinateCross (localFusionSourceCoordinate 0)=coordinateCross (localFusionSourceCoordinate 0) ∧
    coupleCodeBeta • coordinateCross (localFusionSourceCoordinate 1)=coordinateCross (localFusionSourceCoordinate 1) := by
  exact ⟨original_coordinate_cross_fix _ _ coupleCodeBeta_transport coupleOriginal_fixed_coordinates.2.2.1,
    original_second_coordinate_cross_fix _ _ coupleCodeBeta_transport coupleOriginal_fixed_coordinates.2.2.2⟩

theorem coupleCodeR_mem_pair_stabilizer :
    codeR∈MulAction.stabilizer codeGroup (coordinateCross (localFusionSourceCoordinate 0)) ⊓
      MulAction.stabilizer codeGroup (coordinateCross (localFusionSourceCoordinate 1)) :=
  coupleCodeR_fixes_reference

theorem coupleCodeBeta_mem_pair_stabilizer :
    coupleCodeBeta∈MulAction.stabilizer codeGroup (coordinateCross (localFusionSourceCoordinate 0)) ⊓
      MulAction.stabilizer codeGroup (coordinateCross (localFusionSourceCoordinate 1)) :=
  coupleCodeBeta_fixes_reference

end Atlas.Rudvalis
