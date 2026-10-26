import Atlas.LinearGroups.Unitary.Hermitian
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Natural actions of the retained unitary matrix group -/
noncomputable section
namespace Atlas.Unitary
open Matrix
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

instance vectorAction (hdeg : Module.finrank F K = 2) :
    MulAction (U F K n hdeg) (Fin n → K) where
  smul g v := g.val *ᵥ v
  one_smul v := Matrix.one_mulVec v
  mul_smul g h v := (Matrix.mulVec_mulVec v g.val h.val).symm

@[simp] theorem vector_smul (hdeg : Module.finrank F K = 2)
    (g : U F K n hdeg) (v : Fin n → K) : g • v = g.val *ᵥ v := rfl

/-- Actual norm-one vectors, with norm measured by the fixed Hermitian form. -/
def NormOneVectors (F K : Type*) [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (n : ℕ) := {v : Fin n → K // hermitian F K v v = 1}

instance normOneAction (hdeg : Module.finrank F K = 2) :
    MulAction (U F K n hdeg) (NormOneVectors F K n) where
  smul g v := ⟨g.val *ᵥ v.val, (u_preserves_hermitian hdeg g v.val v.val).trans v.prop⟩
  one_smul v := Subtype.ext (Matrix.one_mulVec v.val)
  mul_smul g h v := Subtype.ext (Matrix.mulVec_mulVec v.val g.val h.val).symm

@[simp] theorem normOne_smul_val (hdeg : Module.finrank F K = 2)
    (g : U F K n hdeg) (v : NormOneVectors F K n) :
    (g • v).val = g.val *ᵥ v.val := rfl

/-- Every actual matrix is determined by its natural vector action. -/
instance vectorAction_faithful (hdeg : Module.finrank F K = 2) :
    FaithfulSMul (U F K n hdeg) (Fin n → K) where
  eq_of_smul_eq_smul h := by
    apply Subtype.ext
    apply Matrix.ext_of_mulVec_single
    intro i
    exact h (Pi.single i 1)

/-- Coordinate unit vectors lie on the norm-one shell. -/
def coordinateUnit (i : Fin n) : NormOneVectors F K n :=
  ⟨Pi.single i 1, by simp⟩
end Atlas.Unitary
