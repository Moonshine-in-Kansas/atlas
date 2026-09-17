import Atlas.LinearGroups.Orthogonal.B2ExteriorAction
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # The actual Sp₄ exterior-square homomorphism into the existing O₅ model

The homomorphism is obtained by restriction to the contraction kernel and the
explicit Pfaffian isometry. No assertion about its kernel or image is assumed.
-/
noncomputable section
namespace Atlas.Orthogonal.B2Exterior
open Matrix
variable {F : Type*} [CommRing F]

/-- The actual symplectic matrix, with coordinates ordered e₀,e₁,f₀,f₁. -/
def symplecticMatrix (g : Atlas.Symplectic.Sp 2 F) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.reindexAlgEquiv F F finSumFinEquiv g.val

@[simp] theorem symplecticMatrix_one : symplecticMatrix (1 : Atlas.Symplectic.Sp 2 F) = 1 :=
  map_one (Matrix.reindexAlgEquiv F F finSumFinEquiv)

@[simp] theorem symplecticMatrix_mul (g h : Atlas.Symplectic.Sp 2 F) :
    symplecticMatrix (g * h) = symplecticMatrix g * symplecticMatrix h :=
  map_mul (Matrix.reindexAlgEquiv F F finSumFinEquiv) g.val h.val

theorem symplecticMatrix_det (g : Atlas.Symplectic.Sp 2 F) : (symplecticMatrix g).det = 1 := by
  rw [symplecticMatrix, Matrix.det_reindexAlgEquiv]
  exact Atlas.Symplectic.determinant_one g

omit [CommRing F] in
theorem symplecticCoordinates_eq (v : Atlas.Symplectic.Vector 2 F) :
    symplecticCoordinates v = v ∘ (finSumFinEquiv : Atlas.Symplectic.Index 2 ≃ Fin 4).symm := by
  ext i
  fin_cases i <;> rfl

omit [CommRing F] in
theorem symplecticCoordinates_surjective :
    Function.Surjective (symplecticCoordinates (F := F)) := by
  intro v
  refine ⟨v ∘ (finSumFinEquiv : Atlas.Symplectic.Index 2 ≃ Fin 4), ?_⟩
  rw [symplecticCoordinates_eq]
  ext i
  simp

theorem symplecticMatrix_mulVec (g : Atlas.Symplectic.Sp 2 F)
    (v : Atlas.Symplectic.Vector 2 F) :
    symplecticMatrix g *ᵥ symplecticCoordinates v =
      symplecticCoordinates (g.val *ᵥ v) := by
  rw [symplecticCoordinates_eq, symplecticCoordinates_eq]
  change g.val.submatrix finSumFinEquiv.symm finSumFinEquiv.symm *ᵥ
    (v ∘ finSumFinEquiv.symm) = _
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_def, Equiv.apply_symm_apply]

/-- Contraction is invariant on the entire exterior space for the actual Sp₄ action. -/
theorem symplectic_contraction (g : Atlas.Symplectic.Sp 2 F) (w : Six F) :
    contraction (exteriorMap (symplecticMatrix g) w) = contraction w := by
  apply contraction_exteriorMap
  intro u v
  obtain ⟨u, rfl⟩ := symplecticCoordinates_surjective u
  obtain ⟨v, rfl⟩ := symplecticCoordinates_surjective v
  rw [symplecticMatrix_mulVec, symplecticMatrix_mulVec, contraction_wedge, contraction_wedge]
  exact Atlas.Symplectic.preserves g u v

/-- Pfaffian invariance for the actual symplectic matrices. -/
theorem symplectic_pfaffian (g : Atlas.Symplectic.Sp 2 F) (w : Six F) :
    pfaffian (exteriorMap (symplecticMatrix g) w) = pfaffian w := by
  rw [pfaffian_exteriorMap, symplecticMatrix_det, one_mul]

/-- The restricted linear action on contraction-zero bivectors. -/
def kernelMap (g : Atlas.Symplectic.Sp 2 F) :
    LinearMap.ker (contraction (F := F)) →ₗ[F] LinearMap.ker (contraction (F := F)) where
  toFun w := ⟨exteriorMap (symplecticMatrix g) w.val, by
    change contraction (exteriorMap (symplecticMatrix g) w.val) = 0
    rw [symplectic_contraction]
    exact w.prop⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem kernelMap_mul (g h : Atlas.Symplectic.Sp 2 F) :
    kernelMap (g * h) = (kernelMap g).comp (kernelMap h) := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change exteriorMap (symplecticMatrix (g * h)) w.val =
    exteriorMap (symplecticMatrix g) (exteriorMap (symplecticMatrix h) w.val)
  rw [symplecticMatrix_mul, exteriorMap_mul, LinearMap.comp_apply]

@[simp] theorem kernelMap_one : kernelMap (1 : Atlas.Symplectic.Sp 2 F) = LinearMap.id := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change exteriorMap (symplecticMatrix 1) w.val = w.val
  rw [symplecticMatrix_one, exteriorMap_one, LinearMap.id_apply]

/-- Restriction remains invertible, with inverse induced by the original inverse matrix. -/
def kernelAction (g : Atlas.Symplectic.Sp 2 F) :
    LinearMap.ker (contraction (F := F)) ≃ₗ[F] LinearMap.ker (contraction (F := F)) where
  __ := kernelMap g
  invFun := kernelMap g⁻¹
  left_inv w := by
    change ((kernelMap g⁻¹).comp (kernelMap g)) w = w
    rw [← kernelMap_mul, inv_mul_cancel, kernelMap_one, LinearMap.id_apply]
  right_inv w := by
    change ((kernelMap g).comp (kernelMap g⁻¹)) w = w
    rw [← kernelMap_mul, mul_inv_cancel, kernelMap_one, LinearMap.id_apply]

/-- The induced linear automorphism of the already fixed B₂ carrier. -/
def onB (g : Atlas.Symplectic.Sp 2 F) : VectorB 2 F ≃ₗ[F] VectorB 2 F :=
  kernelEquiv.trans ((kernelAction g).trans kernelEquiv.symm)

theorem onB_pfaffian (g : Atlas.Symplectic.Sp 2 F) (v : VectorB 2 F) :
    formB 2 F (onB g v) = formB 2 F v := by
  rw [← fromB_pfaffian, ← fromB_pfaffian]
  have hv : fromB (onB g v) = exteriorMap (symplecticMatrix g) (fromB v) :=
    congrArg Subtype.val (kernelEquiv.apply_symm_apply (kernelAction g (kernelEquiv v)))
  rw [hv, symplectic_pfaffian]

/-- The actual homomorphism Sp₄ → O(B₂), defined by exterior square and restriction. -/
def toOrthogonal : Atlas.Symplectic.Sp 2 F →* O_B 2 F where
  toFun g := ⟨onB g, onB_pfaffian g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change kernelEquiv.symm (kernelMap 1 (kernelEquiv v)) = v
    rw [kernelMap_one, LinearMap.id_apply, LinearEquiv.symm_apply_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change kernelEquiv.symm (kernelMap (g * h) (kernelEquiv v)) =
      kernelEquiv.symm (kernelMap g (kernelEquiv (kernelEquiv.symm (kernelMap h (kernelEquiv v)))))
    rw [LinearEquiv.apply_symm_apply, kernelMap_mul, LinearMap.comp_apply]

end Atlas.Orthogonal.B2Exterior
