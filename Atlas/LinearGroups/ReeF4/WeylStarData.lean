import Atlas.LinearGroups.ReeF4.WeylForms
import Atlas.LinearGroups.ReeF4.LongRootStarData

/-! Local coefficient data for both Weyl actions on the candidate exterior map.
The only extension defect is rho's diagonal cross column d1 ↦ d0. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F R : Type*} [CommRing F] [CharP F 2] [CommRing R] [CharP R 2]

def weylOperator (g : Fin 2) : TraceZero F ≃ₗ[F] TraceZero F :=
  ![weylRho, weylSigma] g

def weylRootImage (g : Fin 2) (r : ShortRootLabel) : ShortRootLabel :=
  if g = 0 then
    (r.1, (![![0,1,5,4,3,2,6,7], ![1,0,3,2,5,4,7,6],
      ![1,0,4,5,2,3,7,6]] : Fin 3 → Fin 8 → Fin 8) r.1 r.2)
  else
    ((![(2 : Fin 3),1,0]) r.1,
      (![(0 : Fin 8),2,1,4,3,6,5,7]) r.2)

def weylSupport (g : Fin 2) : TraceZeroCoordinate → List TraceZeroCoordinate
  | .inl 0 => if g = 0 then [.inl 0] else [.inl 0, .inl 1]
  | .inl _ => [.inl 1]
  | .inr r => [.inr (weylRootImage g r)]

def weylStarCoefficient (g : Fin 2) (i j : TraceZeroCoordinate) : TraceZero F :=
  ((weylSupport g i).map (fun a =>
    ((weylSupport g j).map (extensionCoefficient a)).sum)).sum

def weylStarCorrection (g : Fin 2) (w : TraceZero F) : TraceZero F :=
  if g = 0 then w.val.1 0 • diagonalVector 0 else 0

def weylStarCorrectionLinear (g : Fin 2) : TraceZero F →ₗ[F] TraceZero F where
  toFun := weylStarCorrection g
  map_add' u v := by
    fin_cases g <;> simp [weylStarCorrection, add_smul]
  map_smul' a u := by
    fin_cases g <;> simp [weylStarCorrection, smul_smul]

theorem weylOperator_map (f : F →+* R) (g : Fin 2) (w : TraceZero F) :
    traceZeroMap f (weylOperator g w) = weylOperator g (traceZeroMap f w) := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    fin_cases g <;> fin_cases i <;> rfl
  · funext i j
    fin_cases g <;> fin_cases i <;> fin_cases j <;> rfl

theorem weylStarCorrection_map (f : F →+* R) (g : Fin 2) (w : TraceZero F) :
    traceZeroMap f (weylStarCorrection g w) =
      weylStarCorrection g (traceZeroMap f w) := by
  fin_cases g
  · change traceZeroScalarMap f (w.val.1 0 • diagonalVector 0) =
      f (w.val.1 0) • diagonalVector 0
    rw [LinearMap.map_smulₛₗ]
    change f (w.val.1 0) • traceZeroMap f (diagonalVector 0) = _
    rw [diagonalVector_map]
  · change traceZeroScalarMap f 0 = 0
    exact map_zero _

theorem weylStarCoefficient_map (f : F →+* R) (g : Fin 2)
    (i j : TraceZeroCoordinate) :
    traceZeroMap f (weylStarCoefficient g i j) = weylStarCoefficient g i j := by
  change traceZeroScalarMap f _ = _
  simp only [weylStarCoefficient, map_list_sum, List.map_map, Function.comp_def]
  simp only [Function.comp_def, traceZeroScalarMap_apply, extensionCoefficient_map]

end Atlas.ReeF4
