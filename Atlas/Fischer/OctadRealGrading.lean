import Atlas.Fischer.RealCoordinateSpace
import Atlas.Fischer.OctadRationalGradeCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped TensorProduct
attribute [local instance] Classical.propDecidable

/-- A real component in the actual scalar extension of the rational model. -/
def octadRealGrade (O : Octad) (S : Finset Omega) : Submodule ℝ RealCoordinates where
  carrier := {x | ∀ p, octadRationalLabel O p ≠ S → realCoordinateEquiv x p = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy p hp
    change realCoordinateEquiv (x+y) p=0
    rw [map_add,Pi.add_apply,hx p hp,hy p hp,add_zero]
  smul_mem' := by
    intro a x hx p hp
    change realCoordinateEquiv (a • x) p=0
    rw [map_smul,Pi.smul_apply,hx p hp,smul_zero]

/-- Restriction and zero extension give the actual coordinate model of each grade. -/
def octadRealGradeEquiv (O : Octad) (S : Finset Omega) :
    octadRealGrade O S ≃ₗ[ℝ] (OctadRationalGradeIndex O S → ℝ) where
  toFun x p := realCoordinateEquiv x.val p.val
  invFun f := ⟨realCoordinateEquiv.symm
    (fun p => if h : octadRationalLabel O p=S then f ⟨p,h⟩ else 0), by
    intro p hp
    rw [LinearEquiv.apply_symm_apply]
    simp [hp]⟩
  left_inv x := by
    apply Subtype.ext
    apply realCoordinateEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    funext p
    by_cases h : octadRationalLabel O p=S
    · simp [h]
    · simp [h,x.prop p h]
  right_inv f := by
    funext p
    change realCoordinateEquiv (realCoordinateEquiv.symm _) p.val=f p
    rw [LinearEquiv.apply_symm_apply]
    simp [p.prop]
  map_add' x y := by
    funext p
    exact congrFun (map_add realCoordinateEquiv x.val y.val) p.val
  map_smul' a x := by
    funext p
    exact congrFun (map_smul realCoordinateEquiv a x.val) p.val

theorem octadRealGrade_finrank (O : Octad) (S : Finset Omega) :
    Module.finrank ℝ (octadRealGrade O S) =
      Nat.card (OctadRationalGradeIndex O S) := by
  letI : Fintype (OctadRationalGradeIndex O S) := Fintype.ofFinite _
  rw [(octadRealGradeEquiv O S).finrank_eq,Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]


theorem octadRealGrade_dimension (O : Octad) (S : Finset Omega) :
    Module.finrank ℝ (octadRealGrade O S) = Module.finrank ℚ (octadRationalGrade O S) := by
  rw [octadRealGrade_finrank, octadRationalGrade_finrank]

/-- Scalar extension sends every actual rational component into its real component. -/
theorem octadRealGrade_tmul (O : Octad) (S : Finset Omega) (a : ℝ)
    {x : Coordinates} (hx : x ∈ octadRationalGrade O S) :
    a ⊗ₜ[ℚ] x ∈ octadRealGrade O S := by
  intro p hp
  rw [realCoordinateEquiv_tmul, hx p hp, Rat.cast_zero, zero_mul]

theorem octadRealGrade_empty_dimension (O : Octad) :
    Module.finrank ℝ (octadRealGrade O ∅) = 55 := by
  rw [octadRealGrade_dimension, octadRationalGrade_empty_dimension]

theorem octadRealGrade_full_dimension (O : Octad) :
    Module.finrank ℝ (octadRealGrade O O.val) = 55 := by
  rw [octadRealGrade_dimension, octadRationalGrade_full_dimension]

theorem octadRealGrade_duad_dimension (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card = 2) :
    Module.finrank ℝ (octadRealGrade O S) = 16 := by
  rw [octadRealGrade_dimension, octadRationalGrade_duad_dimension O S hSO hS]

theorem octadRealGrade_six_dimension (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card = 6) :
    Module.finrank ℝ (octadRealGrade O S) = 16 := by
  rw [octadRealGrade_dimension, octadRationalGrade_six_dimension O S hSO hS]

theorem octadRealGrade_tetrad_dimension (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card = 4) :
    Module.finrank ℝ (octadRealGrade O S) = 8 := by
  rw [octadRealGrade_dimension, octadRationalGrade_tetrad_dimension O S hSO hS]

end Atlas.Fischer
