import Atlas.Sporadic.Janko1.OctonionBasis

/-! The actual pure-imaginary subspace, with the norm in Wilson coordinates. -/
namespace Atlas.Janko1

def traceLinear : SplitOctonion.Carrier Field →ₗ[Field] Field where
  toFun := SplitOctonion.trace
  map_add' x y := by simp [SplitOctonion.trace]; ring
  map_smul' a x := by simp [SplitOctonion.trace]; ring

abbrev Imaginary := traceLinear.ker

theorem imaginary_scalar_coordinate (x : Imaginary) : (wilsonEquiv.symm x.val) 0 = 0 := by
  have h := wilsonEquiv_trace (wilsonEquiv.symm x.val)
  rw [wilsonEquiv.apply_symm_apply] at h
  have hx : SplitOctonion.trace x.val = 0 := x.property
  rw [hx] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by decide)

def imaginaryEquivFin7 : Imaginary ≃ₗ[Field] (Fin 7 → Field) where
  toFun x t := wilsonEquiv.symm x.val t.succ
  invFun v := ⟨wilsonEquiv (Fin.cons 0 v), by
    change SplitOctonion.trace (wilsonEquiv (Fin.cons 0 v)) = 0
    rw [wilsonEquiv_trace]
    simp⟩
  left_inv x := by
    apply Subtype.ext
    apply wilsonEquiv.symm.injective
    rw [wilsonEquiv.symm_apply_apply]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (imaginary_scalar_coordinate x).symm
    · rfl
  right_inv v := by simp
  map_add' x y := by
    funext t
    simp
  map_smul' a x := by
    funext t
    simp

noncomputable def imaginaryBasis : Module.Basis (Fin 7) Field Imaginary :=
  (Pi.basisFun Field (Fin 7)).map imaginaryEquivFin7.symm

def imaginaryNorm (x : Imaginary) : Field := SplitOctonion.norm x.val

theorem imaginaryNorm_coordinates (x : Imaginary) :
    imaginaryNorm x = ∑ t : Fin 7, (imaginaryEquivFin7 x t)^2 := by
  have h := wilsonEquiv_norm (wilsonEquiv.symm x.val)
  rw [wilsonEquiv.apply_symm_apply, Fin.sum_univ_succ, imaginary_scalar_coordinate] at h
  simpa [imaginaryNorm, imaginaryEquivFin7] using h

theorem imaginary_finrank : Module.finrank Field Imaginary = 7 := by
  rw [imaginaryEquivFin7.finrank_eq]
  simp

end Atlas.Janko1
