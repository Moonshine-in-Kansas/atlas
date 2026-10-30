import Atlas.LinearGroups.ReeF4.RootSuzukiScalarProduct
import Atlas.LinearGroups.ReeF4.SpecialMarkedPoints

/-! the constructed direct product lies in the ordered opposite-point
stabilizer. This is only an inclusion, not a full stabilizer theorem. -/
noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
open scoped Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem suzukiLeviCoordinates_extremal_natural (j : Fin 8)
    (hj : j = 0 ∨ j = 7) (k : Fin 4) :
    (suzukiLeviCoordinates (rootVector (F := F) (0,j))).1 k = 0 := by
  rcases hj with rfl | rfl <;> funext i <;> fin_cases k <;> fin_cases i <;>
    simp [suzukiLeviCoordinates,suzukiLeviBlockProject,suzukiLeviBlockLabel,
      rootVector,Pi.single_apply]

private theorem suzukiLeviCoordinates_extremal_exterior (j : Fin 8)
    (hj : j = 0 ∨ j = 7) :
    (suzukiLeviCoordinates (rootVector (F := F) (0,j))).2.1 = 0 := by
  rcases hj with rfl | rfl <;> funext i <;> fin_cases i <;>
    simp [suzukiLeviCoordinates,rootVector,Pi.single_apply,Fin.ext_iff]

theorem suzukiLeviHom_extremal_root (g : Atlas.Symplectic.Sp 2 F)
    (j : Fin 8) (hj : j = 0 ∨ j = 7) :
    suzukiLeviHom g (rootVector (0,j)) = rootVector (0,j) := by
  apply suzukiLeviCoordinatesEquiv.injective
  change suzukiLeviCoordinatesEquiv
    (suzukiLeviLinear (Atlas.SuzukiFamily.matrix g) (rootVector (0,j))) = _
  rw [suzukiLeviLinear_coordinates]
  apply Prod.ext
  · funext k
    change Atlas.SuzukiFamily.matrix g *ᵥ
      (suzukiLeviCoordinates (rootVector (0,j))).1 k =
        (suzukiLeviCoordinates (rootVector (0,j))).1 k
    rw [suzukiLeviCoordinates_extremal_natural j hj k,Matrix.mulVec_zero]
  · apply Prod.ext
    · change suzukiLeviExteriorMatrix (Atlas.SuzukiFamily.matrix g) *ᵥ
        (suzukiLeviCoordinates (rootVector (0,j))).2.1 =
          (suzukiLeviCoordinates (rootVector (0,j))).2.1
      rw [suzukiLeviCoordinates_extremal_exterior j hj,Matrix.mulVec_zero]
    · rfl

theorem modelSuzukiProduct_first_root {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1))
    (g : Atlas.SuzukiFamily.Group F m) (s : Fˣ) :
    (modelSuzukiProductHom hcard (g,s)).val (rootVector (0,0)) =
      ((thetaUnits m s : Fˣ) : F) • rootVector (0,0) := by
  change suzukiLeviHom g.val
    (torusEquiv m (thetaUnits m s) s (rootVector (0,0))) = _
  rw [torusEquiv_root,map_smul,suzukiLeviHom_extremal_root g.val 0 (Or.inl rfl)]
  simp [torusWeight,torusWeightExponents]

theorem modelSuzukiProduct_opposite_root {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1))
    (g : Atlas.SuzukiFamily.Group F m) (s : Fˣ) :
    (modelSuzukiProductHom hcard (g,s)).val (rootVector (0,7)) =
      (((thetaUnits m s)⁻¹ : Fˣ) : F) • rootVector (0,7) := by
  change suzukiLeviHom g.val
    (torusEquiv m (thetaUnits m s) s (rootVector (0,7))) = _
  rw [torusEquiv_root,map_smul,suzukiLeviHom_extremal_root g.val 7 (Or.inr rfl)]
  simp [torusWeight,torusWeightExponents]

theorem modelSuzukiProduct_fixes_first {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1))
    (g : Atlas.SuzukiFamily.Group F m) (s : Fˣ) :
    modelSuzukiProductHom hcard (g,s) • firstSpecialPoint (F := F) m = firstSpecialPoint m := by
  rw [firstSpecialPoint,specialPointMk_smul]
  apply (specialPointMk_eq_iff m _ _ _ _).mpr
  exact ⟨thetaUnits m s,(modelSuzukiProduct_first_root hcard g s).symm⟩

theorem modelSuzukiProduct_fixes_opposite {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1))
    (g : Atlas.SuzukiFamily.Group F m) (s : Fˣ) :
    modelSuzukiProductHom hcard (g,s) • oppositeSpecialPoint (F := F) m = oppositeSpecialPoint m := by
  rw [oppositeSpecialPoint,specialPointMk_smul]
  apply (specialPointMk_eq_iff m _ _ _ _).mpr
  exact ⟨(thetaUnits m s)⁻¹,(modelSuzukiProduct_opposite_root hcard g s).symm⟩

end Atlas.ReeF4
