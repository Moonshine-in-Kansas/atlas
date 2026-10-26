import Atlas.LinearGroups.ReeF4.RootSuzukiLeviExterior
import Mathlib.LinearAlgebra.Matrix.ToLin
import Atlas.LinearGroups.SuzukiFamily.ProjectiveAction

/-! Faithful four-natural-plus-exterior representation in the actual Ree
26-space. Multiplicativity is the degree-two Cauchy--Binet identity, proved
here directly in four coordinates over an arbitrary commutative ring. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Matrix
variable {F : Type*} [CommRing F]

set_option maxHeartbeats 1200000 in
theorem suzukiLeviExteriorMatrix_mul (g h : Matrix (Fin 4) (Fin 4) F) :
    suzukiLeviExteriorMatrix (g*h) =
      suzukiLeviExteriorMatrix g * suzukiLeviExteriorMatrix h := by
  ext i j
  simp only [suzukiLeviExteriorMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  dsimp [suzukiLeviExteriorPair]
  ring

set_option maxHeartbeats 800000 in
theorem suzukiLeviExteriorMatrix_one :
    suzukiLeviExteriorMatrix (1 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiLeviExteriorMatrix, suzukiLeviExteriorPair, Matrix.one_apply]

def suzukiLeviCoordinateLinear (g : Matrix (Fin 4) (Fin 4) F) :
    SuzukiLeviCoordinates F →ₗ[F] SuzukiLeviCoordinates F where
  toFun x := (fun k => g *ᵥ x.1 k,
    (suzukiLeviExteriorMatrix g *ᵥ x.2.1, x.2.2))
  map_add' x y := by
    apply Prod.ext
    · funext k
      change g *ᵥ (x.1 k + y.1 k) = g *ᵥ x.1 k + g *ᵥ y.1 k
      exact Matrix.mulVec_add g (x.1 k) (y.1 k)
    · apply Prod.ext
      · change suzukiLeviExteriorMatrix g *ᵥ (x.2.1 + y.2.1) =
          suzukiLeviExteriorMatrix g *ᵥ x.2.1 + suzukiLeviExteriorMatrix g *ᵥ y.2.1
        exact Matrix.mulVec_add (suzukiLeviExteriorMatrix g) x.2.1 y.2.1
      · rfl
  map_smul' a x := by
    apply Prod.ext
    · funext k
      change g *ᵥ (a • x.1 k) = a • (g *ᵥ x.1 k)
      exact Matrix.mulVec_smul g a (x.1 k)
    · apply Prod.ext
      · change suzukiLeviExteriorMatrix g *ᵥ (a • x.2.1) =
          a • (suzukiLeviExteriorMatrix g *ᵥ x.2.1)
        exact Matrix.mulVec_smul (suzukiLeviExteriorMatrix g) a x.2.1
      · rfl

theorem suzukiLeviCoordinateLinear_mul (g h : Matrix (Fin 4) (Fin 4) F) :
    suzukiLeviCoordinateLinear (g*h) =
      suzukiLeviCoordinateLinear g * suzukiLeviCoordinateLinear h := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · funext k
    change (g*h) *ᵥ x.1 k = g *ᵥ (h *ᵥ x.1 k)
    exact (Matrix.mulVec_mulVec (x.1 k) g h).symm
  · apply Prod.ext
    · change suzukiLeviExteriorMatrix (g*h) *ᵥ x.2.1 =
        suzukiLeviExteriorMatrix g *ᵥ (suzukiLeviExteriorMatrix h *ᵥ x.2.1)
      rw [suzukiLeviExteriorMatrix_mul, Matrix.mulVec_mulVec]
    · rfl

theorem suzukiLeviCoordinateLinear_one :
    suzukiLeviCoordinateLinear (1 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · funext k
    change (1 : Matrix (Fin 4) (Fin 4) F) *ᵥ x.1 k = x.1 k
    exact Matrix.one_mulVec (x.1 k)
  · apply Prod.ext
    · change suzukiLeviExteriorMatrix (1 : Matrix (Fin 4) (Fin 4) F) *ᵥ x.2.1 = x.2.1
      rw [suzukiLeviExteriorMatrix_one, Matrix.one_mulVec]
    · rfl

variable [CharP F 2]

/-- The actual trace-zero-space representation, conjugated by its explicit
26-coordinate decomposition. -/
def suzukiLeviLinear (g : Matrix (Fin 4) (Fin 4) F) : TraceZero F →ₗ[F] TraceZero F :=
  suzukiLeviCoordinatesEquiv.symm.toLinearMap ∘ₗ
    suzukiLeviCoordinateLinear g ∘ₗ suzukiLeviCoordinatesEquiv.toLinearMap

@[simp] theorem suzukiLeviLinear_coordinates (g : Matrix (Fin 4) (Fin 4) F)
    (w : TraceZero F) :
    suzukiLeviCoordinatesEquiv (suzukiLeviLinear g w) =
      suzukiLeviCoordinateLinear g (suzukiLeviCoordinatesEquiv w) := by
  exact LinearEquiv.apply_symm_apply _ _

/-- A natural block detects the representing matrix; hence the full 26-space
representation has trivial kernel, without any simplicity assumption. -/
theorem suzukiLeviLinear_injective : Function.Injective (suzukiLeviLinear (F := F)) := by
  intro g h heq
  have hv : ∀ v : Fin 4 → F, g *ᵥ v = h *ᵥ v := by
    intro v
    have hw := congrArg (fun f : TraceZero F →ₗ[F] TraceZero F =>
      suzukiLeviCoordinatesEquiv (f (suzukiLeviBlockEmbed 0 v))) heq
    rw [suzukiLeviLinear_coordinates, suzukiLeviLinear_coordinates] at hw
    have hk := congrArg (fun x : SuzukiLeviCoordinates F => x.1 0) hw
    change g *ᵥ suzukiLeviBlockProject 0 (suzukiLeviBlockEmbed 0 v) =
      h *ᵥ suzukiLeviBlockProject 0 (suzukiLeviBlockEmbed 0 v) at hk
    simpa only [suzukiLeviBlockProject_embed] using hk
  apply Matrix.toLinAlgEquiv'.injective
  apply LinearMap.ext
  intro v
  exact hv v


theorem suzukiLeviLinear_mul (g h : Matrix (Fin 4) (Fin 4) F) :
    suzukiLeviLinear (g*h) = suzukiLeviLinear g * suzukiLeviLinear h := by
  apply LinearMap.ext
  intro w
  apply suzukiLeviCoordinatesEquiv.injective
  simp only [Module.End.mul_apply, suzukiLeviLinear_coordinates,
    suzukiLeviCoordinateLinear_mul]

theorem suzukiLeviLinear_one :
    suzukiLeviLinear (1 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  apply LinearMap.ext
  intro w
  apply suzukiLeviCoordinatesEquiv.injective
  rw [suzukiLeviLinear_coordinates, suzukiLeviCoordinateLinear_one]
  rfl

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- A faithful representation of the ambient Sp4 on the actual 26-space.
Membership in the Ree stabilizer is only claimed later for the Suzuki subgroup. -/
def suzukiLeviEquiv (g : Atlas.Symplectic.Sp 2 K) : TraceZero K ≃ₗ[K] TraceZero K where
  toFun := suzukiLeviLinear (Atlas.SuzukiFamily.matrix g)
  invFun := suzukiLeviLinear (Atlas.SuzukiFamily.matrix g⁻¹)
  left_inv w := by
    change (suzukiLeviLinear (Atlas.SuzukiFamily.matrix g⁻¹) *
      suzukiLeviLinear (Atlas.SuzukiFamily.matrix g)) w = w
    rw [← suzukiLeviLinear_mul, ← Atlas.SuzukiFamily.matrix_mul]
    simp only [inv_mul_cancel, Atlas.SuzukiFamily.matrix_one, suzukiLeviLinear_one]
    rfl
  right_inv w := by
    change (suzukiLeviLinear (Atlas.SuzukiFamily.matrix g) *
      suzukiLeviLinear (Atlas.SuzukiFamily.matrix g⁻¹)) w = w
    rw [← suzukiLeviLinear_mul, ← Atlas.SuzukiFamily.matrix_mul]
    simp only [mul_inv_cancel, Atlas.SuzukiFamily.matrix_one, suzukiLeviLinear_one]
    rfl
  map_add' := (suzukiLeviLinear (Atlas.SuzukiFamily.matrix g)).map_add
  map_smul' := (suzukiLeviLinear (Atlas.SuzukiFamily.matrix g)).map_smul

def suzukiLeviHom : Atlas.Symplectic.Sp 2 K →* (TraceZero K ≃ₗ[K] TraceZero K) where
  toFun := suzukiLeviEquiv
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    change suzukiLeviLinear (Atlas.SuzukiFamily.matrix 1) = 1
    rw [Atlas.SuzukiFamily.matrix_one, suzukiLeviLinear_one]
  map_mul' g h := by
    apply LinearEquiv.toLinearMap_injective
    change suzukiLeviLinear (Atlas.SuzukiFamily.matrix (g*h)) =
      suzukiLeviLinear (Atlas.SuzukiFamily.matrix g) *
        suzukiLeviLinear (Atlas.SuzukiFamily.matrix h)
    rw [Atlas.SuzukiFamily.matrix_mul, suzukiLeviLinear_mul]

theorem suzukiLeviHom_injective : Function.Injective (suzukiLeviHom (K := K)) := by
  intro g h heq
  have he := congrArg LinearEquiv.toLinearMap heq
  have hm := suzukiLeviLinear_injective he
  apply Subtype.ext
  exact (Atlas.SuzukiFamily.toStandard (F := K)).symm.injective hm

end FiniteField
end Atlas.ReeF4
