import Atlas.LinearGroups.ProjectiveSpecialLinear

/-! # Entrywise field transport for the retained special linear quotients -/
noncomputable section
namespace Atlas
open scoped MatrixGroups
variable {F K : Type*} [Field F] [Field K]

def fieldEquivSL (n : ℕ) (e : F ≃+* K) : SL(n,F) ≃* SL(n,K) where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by ext i j; exact e.symm_apply_apply _
  right_inv g := by ext i j; exact e.apply_symm_apply _
  map_mul' g h := (Matrix.SpecialLinearGroup.map e.toRingHom).map_mul g h

def fieldEquivPSL (n : ℕ) (e : F ≃+* K) : PSL(n,F) ≃* PSL(n,K) :=
  QuotientGroup.congr _ _ (fieldEquivSL n e) (Subgroup.map_center_eq (fieldEquivSL n e))

@[simp] theorem fieldEquivPSL_projection (n : ℕ) (e : F ≃+* K) (g : SL(n,F)) :
    fieldEquivPSL n e (QuotientGroup.mk' (Subgroup.center (SL(n,F))) g) =
      QuotientGroup.mk' (Subgroup.center (SL(n,K))) (fieldEquivSL n e g) := rfl
end Atlas
