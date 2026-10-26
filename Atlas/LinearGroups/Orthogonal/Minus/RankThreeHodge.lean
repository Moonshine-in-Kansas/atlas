import Atlas.LinearGroups.Orthogonal.Minus.NormPlane
import Atlas.LinearGroups.Orthogonal.B2ExteriorCoordinates
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Concrete semilinear Hodge fixed space in the standard six minor coordinates. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic Atlas.Orthogonal.B2Exterior Matrix
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def hodge (w : Six K) : Six K :=
  ![conjugation F K (w 5),-conjugation F K (w 4),conjugation F K (w 3),
    conjugation F K (w 2),-conjugation F K (w 1),conjugation F K (w 0)]

theorem hodge_add (v w : Six K) : hodge (F := F) (v+w) = hodge (F := F) v + hodge (F := F) w := by
  ext i
  fin_cases i <;> simp [hodge,map_add,add_comm]

theorem hodge_smul (a : K) (w : Six K) :
    hodge (F := F) (a • w) = conjugation F K a • hodge (F := F) w := by
  ext i
  fin_cases i <;> simp [hodge,map_mul]

theorem hodge_base_smul (a : F) (w : Six K) : hodge (F := F) (a • w) = a • hodge (F := F) w := by
  ext i
  fin_cases i <;> simp [hodge,Algebra.smul_def,map_mul]

theorem hodge_involutive (hdeg : Module.finrank F K = 2) : Function.Involutive (hodge (F := F) (K := K)) := by
  intro w
  ext i
  fin_cases i <;> simp [hodge,conjugation_conjugation hdeg]

def hodgeLinear : Six K →ₗ[F] Six K where
  toFun := hodge (F := F)
  map_add' := hodge_add
  map_smul' := hodge_base_smul

def hodgeFixed (_hdeg : Module.finrank F K = 2) : Submodule F (Six K) where
  carrier := {w | hodge (F := F) w = w}
  zero_mem' := by ext i; fin_cases i <;> simp [hodge]
  add_mem' hv hw := by
    change hodge (F := F) (_+_) = _+_
    rw [hodge_add,hv,hw]
  smul_mem' a w hw := by
    change hodge (F := F) (a • w) = a • w
    rw [hodge_base_smul,hw]

@[simp] theorem mem_hodgeFixed (hdeg : Module.finrank F K = 2) (w : Six K) :
    w ∈ hodgeFixed hdeg ↔ hodge (F := F) w = w := Iff.rfl

def fixedVector (v : Fin 3 → K) : Six K :=
  ![v 0,v 1,v 2,conjugation F K (v 2),-conjugation F K (v 1),conjugation F K (v 0)]

def firstThree (w : Six K) : Fin 3 → K := ![w 0,w 1,w 2]

theorem fixedVector_fixed (hdeg : Module.finrank F K = 2) (v : Fin 3 → K) :
    hodge (F := F) (fixedVector (F := F) v) = fixedVector (F := F) v := by
  ext i
  fin_cases i <;> simp [hodge,fixedVector,conjugation_conjugation hdeg]

def hodgeCoordinates (hdeg : Module.finrank F K = 2) :
    (Fin 3 → K) ≃ₗ[F] hodgeFixed hdeg where
  toFun v := ⟨fixedVector (F := F) v,fixedVector_fixed hdeg v⟩
  invFun w := firstThree w.val
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv w := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact congrFun w.prop 3
    · exact congrFun w.prop 4
    · exact congrFun w.prop 5
  map_add' v w := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [fixedVector,map_add,add_comm]
  map_smul' a v := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [fixedVector,Algebra.smul_def,map_mul]

theorem hodgeFixed_finrank (hdeg : Module.finrank F K = 2) :
    Module.finrank F (hodgeFixed hdeg) = 6 := by
  rw [← (hodgeCoordinates hdeg).finrank_eq]
  simp [Module.finrank_pi_fintype,hdeg]

def normTripleForm (hdeg : Module.finrank F K = 2) : QuadraticForm F (Fin 3 → K) :=
  (normForm hdeg).comp (LinearMap.proj 0) +
  (normForm hdeg).comp (LinearMap.proj 1) +
  (normForm hdeg).comp (LinearMap.proj 2)

@[simp] theorem normTripleForm_apply (hdeg : Module.finrank F K = 2) (v : Fin 3 → K) :
    normTripleForm hdeg v = norm F K (v 0)+norm F K (v 1)+norm F K (v 2) := by
  simp [normTripleForm]

theorem fixedVector_pfaffian (hdeg : Module.finrank F K = 2) (v : Fin 3 → K) :
    pfaffian (fixedVector (F := F) v) = algebraMap F K (normTripleForm hdeg v) := by
  simp [pfaffian_apply,fixedVector,normTripleForm_apply,map_add,norm_formula hdeg]

def hodgeFixedForm (hdeg : Module.finrank F K = 2) : QuadraticForm F (hodgeFixed hdeg) :=
  (normTripleForm hdeg).comp (hodgeCoordinates hdeg).symm.toLinearMap

theorem hodgeFixedForm_pfaffian (hdeg : Module.finrank F K = 2) (w : hodgeFixed hdeg) :
    algebraMap F K (hodgeFixedForm hdeg w) = pfaffian w.val := by
  change algebraMap F K (normTripleForm hdeg ((hodgeCoordinates hdeg).symm w)) = _
  rw [← fixedVector_pfaffian hdeg]
  exact congrArg (fun z : hodgeFixed hdeg => pfaffian z.val)
    ((hodgeCoordinates hdeg).apply_symm_apply w)

def hodgeCoordinatesIsometry (hdeg : Module.finrank F K = 2) :
    (normTripleForm hdeg).IsometryEquiv (hodgeFixedForm hdeg) where
  __ := hodgeCoordinates hdeg
  map_app' v := by
    change normTripleForm hdeg ((hodgeCoordinates hdeg).symm ((hodgeCoordinates hdeg) v)) = _
    rw [LinearEquiv.symm_apply_apply]

end Atlas.Orthogonal.Minus
