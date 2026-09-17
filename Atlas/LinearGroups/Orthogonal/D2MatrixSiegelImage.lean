import Atlas.LinearGroups.Orthogonal.D2MatrixAction
import Atlas.LinearGroups.Orthogonal.ElementaryNormal
import Atlas.LinearGroups.Orthogonal.StandardComplement
import Atlas.LinearAlgebra.RankOneMatrixTwo

/-! # Every actual split-D₂ Siegel generator belongs to the left-right matrix image -/
noncomputable section
namespace Atlas.Orthogonal.D2Matrix
open Atlas.Quadratic Matrix
variable {F : Type*} [Field F]

/-- The root at the fixed rank-one direction is an explicit pair of SL₂ transvections. -/
theorem standard_siegel_image (v : VectorD 2 F)
    (hv : (formD 2 F).polarBilin (e 0) v = 0) :
    siegelElement (formD 2 F) (e 0) v (formD_e 0) hv =
      toOrthogonal (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (-v (.inl 1)),
        SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (-v (.inr 1))) := by
  have hv0 : v (.inr 0) = 0 := by
    have hh := hv
    simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, formD_apply, e, Fin.sum_univ_two] at hh
    linear_combination hh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i | i <;> fin_cases i
  all_goals
    change siegel (formD 2 F) (e 0) v x _ = _
    simp [siegel, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, Matrix.adjugate_fin_two, formD_apply, e, Fin.sum_univ_two, hv0,
      toOrthogonal, onD, coordinates, matrixAction, SpecialLinearGroup.transvection_inv,
      SpecialLinearGroup.transvection_coe, Matrix.transvection, Matrix.mul_apply,
      Matrix.vecHead, Matrix.vecTail]
    <;> ring

/-- The actual left-right matrix image transports the fixed singular vector to every nonzero singular vector. -/
theorem singular_image_orbit (u : VectorD 2 F) (hu : u ≠ 0) (hqu : formD 2 F u = 0) :
    ∃ g : PairSL (F := F), (toOrthogonal g).val (e 0) = u := by
  have hm : coordinates u ≠ 0 := by
    intro h
    exact hu (coordinates.injective (h.trans (map_zero coordinates).symm))
  obtain ⟨A,B,h⟩ := Atlas.MatrixTwo.singular_nonzero_SL2_orbit (coordinates u) hm
    ((coordinates_det u).trans hqu)
  refine ⟨(A,B), ?_⟩
  apply coordinates.injective
  rw [toOrthogonal_coordinates]
  have he : coordinates (e (F := F) (0 : Fin 2)) = Atlas.MatrixTwo.E11 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordinates, e, Atlas.MatrixTwo.E11]
  rw [he]
  exact h.symm

/-- Singular transport and the explicit standard root place every Siegel generator in the image. -/
theorem siegel_mem_image (u v : VectorD 2 F) (hu : formD 2 F u = 0)
    (huv : (formD 2 F).polarBilin u v = 0) :
    siegelElement (formD 2 F) u v hu huv ∈ (toOrthogonal (F := F)).range := by
  by_cases hu0 : u = 0
  · have he : siegelElement (formD 2 F) u v hu huv = 1 := by
      subst u
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change siegel (formD 2 F) 0 v x = x
      simp [siegel]
    rw [he]
    exact (toOrthogonal (F := F)).range.one_mem
  · obtain ⟨a,ha⟩ := singular_image_orbit u hu0 hu
    let g := toOrthogonal a
    change g.val (e 0) = u at ha
    let w := g.val.symm v
    have hw : (formD 2 F).polarBilin (e 0) w = 0 := by
      have hh := isometry_polar (formD 2 F) (isometryCarrierEquiv _ g) (e 0) w
      change (formD 2 F).polarBilin (g.val (e 0)) (g.val (g.val.symm v)) =
        (formD 2 F).polarBilin (e 0) w at hh
      rw [LinearEquiv.apply_symm_apply, ha, huv] at hh
      exact hh.symm
    have hs : siegelElement (formD 2 F) (e 0) w (formD_e 0) hw ∈
        (toOrthogonal (F := F)).range := by
      rw [standard_siegel_image]
      exact ⟨_,rfl⟩
    have hg : g ∈ (toOrthogonal (F := F)).range := ⟨a,rfl⟩
    have he := siegelElement_conj (formD 2 F) g (e 0) w (formD_e 0) hw
    have he' : g * siegelElement (formD 2 F) (e 0) w (formD_e 0) hw * g⁻¹ =
        siegelElement (formD 2 F) u v hu huv := by
      simpa only [ha, w, LinearEquiv.apply_symm_apply] using he
    rw [← he']
    exact (toOrthogonal (F := F)).range.mul_mem
      ((toOrthogonal (F := F)).range.mul_mem hg hs) ((toOrthogonal (F := F)).range.inv_mem hg)

/-- The whole actual elementary D₂ subgroup lies in the genuine SL₂ × SL₂ matrix image. -/
theorem elementary_le_image : elementarySubgroup (formD 2 F) ≤ (toOrthogonal (F := F)).range := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u,v,hu,huv,rfl⟩
  exact siegel_mem_image u v hu huv

end Atlas.Orthogonal.D2Matrix

