import Atlas.LinearGroups.ReeF4.WeylSL2Blocks
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! The faithful SL₂ representation behind the source long-root subgroup.
This file only constructs the representation; membership in the full stabilizer
must subsequently be established from the actual root and torus operators. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F]

abbrev LongSL2 := Matrix.SpecialLinearGroup (Fin 2) F

def longSL2TensorMatrix (A B : LongSL2 (F := F)) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F :=
  Matrix.kronecker (A : Matrix (Fin 2) (Fin 2) F) (B : Matrix (Fin 2) (Fin 2) F)

theorem longSL2TensorMatrix_mul (A B C D : LongSL2 (F := F)) :
    longSL2TensorMatrix (A*C) (B*D) = longSL2TensorMatrix A B * longSL2TensorMatrix C D := by
  exact Matrix.mul_kronecker_mul _ _ _ _

@[simp] theorem longSL2TensorMatrix_one :
    longSL2TensorMatrix (1 : LongSL2 (F := F)) 1 = 1 := Matrix.one_kronecker_one

def longSL2TensorEquiv (A B : LongSL2 (F := F)) :
    ((Fin 2 × Fin 2) → F) ≃ₗ[F] ((Fin 2 × Fin 2) → F) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (longSL2TensorMatrix A B))
    (Matrix.toLin' (longSL2TensorMatrix A⁻¹ B⁻¹))
    (by rw [← Matrix.toLin'_mul, ← longSL2TensorMatrix_mul,
      mul_inv_cancel, mul_inv_cancel, longSL2TensorMatrix_one, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← longSL2TensorMatrix_mul,
      inv_mul_cancel, inv_mul_cancel, longSL2TensorMatrix_one, Matrix.toLin'_one])

theorem longSL2TensorEquiv_mul (A B C D : LongSL2 (F := F)) :
    longSL2TensorEquiv (A*C) (B*D) = longSL2TensorEquiv A B * longSL2TensorEquiv C D := by
  apply LinearEquiv.toLinearMap_injective
  exact (congrArg Matrix.toLin' (longSL2TensorMatrix_mul A B C D)).trans
    (Matrix.toLin'_mul _ _)

@[simp] theorem longSL2TensorEquiv_one :
    longSL2TensorEquiv (1 : LongSL2 (F := F)) 1 = 1 := by
  apply LinearEquiv.toLinearMap_injective
  exact (congrArg Matrix.toLin' longSL2TensorMatrix_one).trans Matrix.toLin'_one

def longSL2Curry : ((Fin 2 × Fin 2) → F) ≃ₗ[F] (Fin 2 → Fin 2 → F) where
  toFun v i j := v (i,j)
  invFun v p := v p.1 p.2
  left_inv v := rfl
  right_inv v := rfl
  map_add' u v := rfl
  map_smul' a v := rfl

def longSL2TensorCurried (A B : LongSL2 (F := F)) :
    (Fin 2 → Fin 2 → F) ≃ₗ[F] (Fin 2 → Fin 2 → F) :=
  longSL2Curry.symm.trans ((longSL2TensorEquiv A B).trans longSL2Curry)

theorem longSL2TensorCurried_mul (A B C D : LongSL2 (F := F)) :
    longSL2TensorCurried (A*C) (B*D) =
      longSL2TensorCurried A B * longSL2TensorCurried C D := by
  apply LinearEquiv.ext
  intro v
  funext i j
  exact congrFun (congrArg
    (fun e : ((Fin 2 × Fin 2) → F) ≃ₗ[F] ((Fin 2 × Fin 2) → F) =>
      e (fun p => v p.1 p.2)) (longSL2TensorEquiv_mul A B C D)) (i,j)

@[simp] theorem longSL2TensorCurried_one :
    longSL2TensorCurried (1 : LongSL2 (F := F)) 1 = 1 := by
  apply LinearEquiv.ext
  intro v
  funext i j
  exact congrFun (congrArg
    (fun e : ((Fin 2 × Fin 2) → F) ≃ₗ[F] ((Fin 2 × Fin 2) → F) =>
      e (fun p => v p.1 p.2)) longSL2TensorEquiv_one) (i,j)

variable [CharP F 2]

def longSL2BlocksAction (σ : F →+* F) (A : LongSL2 (F := F)) :
    LongSL2Blocks F ≃ₗ[F] LongSL2Blocks F :=
  (LinearEquiv.piCongrRight (fun _ : Fin 4 => Matrix.SpecialLinearGroup.toLin' A)).prodCongr
    ((LinearEquiv.piCongrRight (fun _ : Fin 2 =>
      Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.map σ A))).prodCongr
    ((LinearEquiv.piCongrRight (fun _ : Fin 2 =>
      longSL2TensorCurried A (Matrix.SpecialLinearGroup.map σ A))).prodCongr
    ((longSL2TensorCurried A A).prodCongr (LinearEquiv.refl F (Fin 2 → F)))))

theorem longSL2BlocksAction_mul (σ : F →+* F) (A B : LongSL2 (F := F)) :
    longSL2BlocksAction σ (A*B) = longSL2BlocksAction σ A * longSL2BlocksAction σ B := by
  apply LinearEquiv.ext
  intro v
  apply Prod.ext
  · funext i
    exact congrArg (fun e => e (v.1 i)) (map_mul Matrix.SpecialLinearGroup.toLin' A B)
  · apply Prod.ext
    · funext i
      change Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.map σ (A*B))
        (v.2.1 i) = _
      simp only [map_mul, LinearEquiv.mul_apply]
      rfl
    · apply Prod.ext
      · funext i
        change longSL2TensorCurried (A*B) (Matrix.SpecialLinearGroup.map σ (A*B))
          (v.2.2.1 i) = _
        rw [map_mul, longSL2TensorCurried_mul]
        rfl
      · apply Prod.ext
        · change longSL2TensorCurried (A*B) (A*B) v.2.2.2.1 = _
          rw [longSL2TensorCurried_mul]
          rfl
        · rfl

@[simp] theorem longSL2BlocksAction_one (σ : F →+* F) :
    longSL2BlocksAction σ (1 : LongSL2 (F := F)) = 1 := by
  apply LinearEquiv.ext
  intro v
  apply Prod.ext
  · funext i
    change Matrix.SpecialLinearGroup.toLin' 1 (v.1 i) = _
    rw [map_one]
    rfl
  · apply Prod.ext
    · funext i
      change Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.map σ 1) (v.2.1 i) = _
      rw [map_one, map_one]
      rfl
    · apply Prod.ext
      · funext i
        change longSL2TensorCurried 1 (Matrix.SpecialLinearGroup.map σ 1) (v.2.2.1 i) = _
        rw [map_one, longSL2TensorCurried_one]
        rfl
      · apply Prod.ext
        · change longSL2TensorCurried 1 1 v.2.2.2.1 = _
          rw [longSL2TensorCurried_one]
          rfl
        · rfl

def longSL2BlocksHom (σ : F →+* F) : LongSL2 (F := F) →*
    (LongSL2Blocks F ≃ₗ[F] LongSL2Blocks F) where
  toFun := longSL2BlocksAction σ
  map_one' := longSL2BlocksAction_one σ
  map_mul' := longSL2BlocksAction_mul σ

theorem longSL2BlocksHom_injective (σ : F →+* F) :
    Function.Injective (longSL2BlocksHom σ) := by
  intro A B h
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  exact congrArg
    (fun e : LongSL2Blocks F ≃ₗ[F] LongSL2Blocks F =>
      (e (![v,0,0,0],0,0,0,0)).1 0) h

def longSL2Representation (σ : F →+* F) : LongSL2 (F := F) →*
    (TraceZero F ≃ₗ[F] TraceZero F) where
  toFun A := longSL2BlocksEquiv.trans
    ((longSL2BlocksHom σ A).trans longSL2BlocksEquiv.symm)
  map_one' := by
    apply LinearEquiv.ext
    intro w
    simp only [map_one, LinearEquiv.trans_apply, LinearEquiv.coe_one, id_eq,
      LinearEquiv.symm_apply_apply]
  map_mul' A B := by
    apply LinearEquiv.ext
    intro w
    simp only [map_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.apply_symm_apply]

theorem longSL2Representation_injective (σ : F →+* F) :
    Function.Injective (longSL2Representation σ) := by
  intro A B h
  apply longSL2BlocksHom_injective σ
  apply LinearEquiv.ext
  intro v
  have hv := congrArg
    (fun e : TraceZero F ≃ₗ[F] TraceZero F =>
      longSL2BlocksEquiv (e (longSL2BlocksEquiv.symm v))) h
  simpa only [longSL2Representation, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using hv

end Atlas.ReeF4
