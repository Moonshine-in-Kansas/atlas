import Atlas.Fischer.RationalCoordinateBasis
import Atlas.Fischer.OctadRestrictionCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Labels of the actual rational directions: axes have empty label, octad
coordinates have their intersection label, and theta takes complement in O. -/
def octadRationalLabel (O : Octad) (p : RationalCoordinateIndex) : Finset Omega :=
  let S := match p.1 with
    | Sum.inl _ => ∅
    | Sum.inr D => D.val ∩ O.val
  if p.2=0 then S else O.val \ S

@[simp] theorem octadRationalLabel_axis_real (O : Octad) (i : Omega) :
    octadRationalLabel O (Sum.inl i,0) = ∅ := rfl

@[simp] theorem octadRationalLabel_axis_theta (O : Octad) (i : Omega) :
    octadRationalLabel O (Sum.inl i,1) = O.val := by simp [octadRationalLabel]

@[simp] theorem octadRationalLabel_octad_real (O D : Octad) :
    octadRationalLabel O (Sum.inr D,0) = D.val ∩ O.val := rfl

@[simp] theorem octadRationalLabel_octad_theta (O D : Octad) :
    octadRationalLabel O (Sum.inr D,1) = O.val \ (D.val ∩ O.val) := rfl

/-- This is a rational subspace of the existing E-coordinate model. -/
def octadRationalGrade (O : Octad) (S : Finset Omega) : Submodule ℚ Coordinates where
  carrier := {x | ∀ p, octadRationalLabel O p ≠ S → rationalCoordinateEquiv x p = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy p hp
    change rationalCoordinateEquiv (x+y) p=0
    rw [map_add,Pi.add_apply,hx p hp,hy p hp,add_zero]
  smul_mem' := by
    intro a x hx p hp
    change rationalCoordinateEquiv (a • x) p=0
    rw [map_smul,Pi.smul_apply,hx p hp,smul_zero]

abbrev OctadRationalGradeIndex (O : Octad) (S : Finset Omega) :=
  {p : RationalCoordinateIndex // octadRationalLabel O p=S}

/-- Restriction and zero extension give the actual coordinate model of each grade. -/
def octadRationalGradeEquiv (O : Octad) (S : Finset Omega) :
    octadRationalGrade O S ≃ₗ[ℚ] (OctadRationalGradeIndex O S → ℚ) where
  toFun x p := rationalCoordinateEquiv x.val p.val
  invFun f := ⟨rationalCoordinateEquiv.symm
    (fun p => if h : octadRationalLabel O p=S then f ⟨p,h⟩ else 0), by
    intro p hp
    rw [LinearEquiv.apply_symm_apply]
    simp [hp]⟩
  left_inv x := by
    apply Subtype.ext
    apply rationalCoordinateEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    funext p
    by_cases h : octadRationalLabel O p=S
    · simp [h]
    · simp [h,x.prop p h]
  right_inv f := by
    funext p
    change rationalCoordinateEquiv (rationalCoordinateEquiv.symm _) p.val=f p
    rw [LinearEquiv.apply_symm_apply]
    simp [p.prop]
  map_add' x y := by
    funext p
    exact congrFun (map_add rationalCoordinateEquiv x.val y.val) p.val
  map_smul' a x := by
    funext p
    exact congrFun (map_smul rationalCoordinateEquiv a x.val) p.val

theorem octadRationalGrade_finrank (O : Octad) (S : Finset Omega) :
    Module.finrank ℚ (octadRationalGrade O S) =
      Nat.card (OctadRationalGradeIndex O S) := by
  letI : Fintype (OctadRationalGradeIndex O S) := Fintype.ofFinite _
  rw [(octadRationalGradeEquiv O S).finrank_eq,Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

end Atlas.Fischer
