import Atlas.LinearGroups.SuzukiFamily.Model
import Atlas.LinearGroups.SuzukiFamily.Ovoid

/-! Actual column action transported from the retained symplectic matrix carrier. -/
noncomputable section
namespace Atlas.SuzukiFamily
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def matrix (g : Atlas.Symplectic.Sp 2 F) : Matrix (Fin 4) (Fin 4) F :=
  toStandard.symm g.val
@[simp] theorem matrix_mul (g h : Atlas.Symplectic.Sp 2 F) : matrix (g*h)=matrix g*matrix h :=
  toStandard.symm.map_mul g.val h.val
@[simp] theorem matrix_one : matrix (1 : Atlas.Symplectic.Sp 2 F)=1 := by
  change (toStandard (F := F)).symm 1=1
  exact map_one _
@[simp] theorem matrix_root (m : ℕ) (a b : F) : matrix (rootElement m a b)=u m a b :=
  toStandard.symm_apply_apply _
@[simp] theorem matrix_torus (m : ℕ) (t : Fˣ) : matrix (torusElement m t)=h m t :=
  toStandard.symm_apply_apply _
@[simp] theorem matrix_weyl : matrix (weylElement : Atlas.Symplectic.Sp 2 F)=w :=
  toStandard.symm_apply_apply _

def columnEquiv (g : Atlas.Symplectic.Sp 2 F) : Vector F ≃ₗ[F] Vector F where
  toFun v := matrix g *ᵥ v
  invFun v := matrix g⁻¹ *ᵥ v
  left_inv v := by dsimp only; rw [Matrix.mulVec_mulVec,← matrix_mul]; simp
  right_inv v := by dsimp only; rw [Matrix.mulVec_mulVec,← matrix_mul]; simp
  map_add' v z := Matrix.mulVec_add _ _ _
  map_smul' t v := Matrix.mulVec_smul _ _ _

def pointLeft (g : Atlas.Symplectic.Sp 2 F) : Projective F → Projective F :=
  Projectivization.map (columnEquiv g).toLinearMap (columnEquiv g).injective

theorem pointLeft_one : pointLeft (1 : Atlas.Symplectic.Sp 2 F)=id := by
  funext p
  induction p using Projectivization.ind with
  | h v hv =>
    change Projectivization.mk F (matrix 1 *ᵥ v) _ = Projectivization.mk F v hv
    simp only [matrix_one,Matrix.one_mulVec]

theorem pointLeft_mul (g h : Atlas.Symplectic.Sp 2 F) :
    pointLeft (g*h)=pointLeft g ∘ pointLeft h := by
  funext p
  induction p using Projectivization.ind with
  | h v hv =>
    change Projectivization.mk F (matrix (g*h) *ᵥ v) _ =
      Projectivization.mk F (matrix g *ᵥ (matrix h *ᵥ v)) _
    simp only [matrix_mul,Matrix.mulVec_mulVec]

theorem pointLeft_injective (g : Atlas.Symplectic.Sp 2 F) : Function.Injective (pointLeft g) :=
  Projectivization.map_injective (columnEquiv g).toLinearMap (columnEquiv g).injective
end Atlas.SuzukiFamily
