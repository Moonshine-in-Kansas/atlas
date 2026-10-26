import Atlas.LinearGroups.Orthogonal.Minus.NormPlane
import Atlas.LinearGroups.Orthogonal.Radical
import Atlas.LinearGroups.Orthogonal.Elementary
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The nonsplit quadratic space: k hyperbolic pairs and the actual norm plane.
The half-dimension is k+1. No intrinsic-kernel or order assertion is a definition. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

abbrev Vector (k : ℕ) (F K : Type*) := VectorD k F × K

def form (hdeg : Module.finrank F K = 2) (k : ℕ) : QuadraticForm F (Vector k F K) :=
  (formD k F).comp (LinearMap.fst F _ _) +
    (normForm hdeg).comp (LinearMap.snd F _ _)

@[simp] theorem form_apply (hdeg : Module.finrank F K = 2) (k : ℕ) (v : Vector k F K) :
    form hdeg k v = formD k F v.1 + norm F K v.2 := by
  simp [form]

theorem polar_apply (hdeg : Module.finrank F K = 2) (k : ℕ) (v w : Vector k F K) :
    (form hdeg k).polarBilin v w =
      (formD k F).polarBilin v.1 w.1 + (normForm hdeg).polarBilin v.2 w.2 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    form_apply, Prod.fst_add, Prod.snd_add, normForm_apply]
  ring

theorem polar_separating (hdeg : Module.finrank F K = 2) (k : ℕ)
    (v : Vector k F K) (hv : ∀ w, (form hdeg k).polarBilin v w = 0) : v = 0 := by
  apply Prod.ext
  · apply polarD_separating
    intro w
    simpa only [polar_apply, map_zero, add_zero] using hv (w,0)
  · apply (normForm_polar_nondegenerate hdeg).1
    intro w
    simpa only [polar_apply, map_zero, zero_add] using hv (0,w)

theorem polar_nondegenerate (hdeg : Module.finrank F K = 2) (k : ℕ) :
    (form hdeg k).polarBilin.Nondegenerate := by
  constructor
  · exact polar_separating hdeg k
  · intro v hv
    apply polar_separating hdeg k v
    intro w
    simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using hv w

theorem vector_finrank (hdeg : Module.finrank F K = 2) (k : ℕ) :
    Module.finrank F (Vector k F K) = 2*(k+1) := by
  simp [Vector, VectorD, Index, Module.finrank_prod, Module.finrank_pi, hdeg,
    Fintype.card_sum]
  omega

abbrev O (hdeg : Module.finrank F K = 2) (k : ℕ) := isometrySubgroup (form hdeg k)
abbrev E (hdeg : Module.finrank F K = 2) (k : ℕ) := elementarySubgroup (form hdeg k)

instance finite_O (hdeg : Module.finrank F K = 2) (k : ℕ) : Finite (O hdeg k) :=
  Finite.of_injective (fun g : O hdeg k => (g.val : Vector k F K → Vector k F K))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

instance finite_E (hdeg : Module.finrank F K = 2) (k : ℕ) : Finite (E hdeg k) :=
  inferInstance

end Atlas.Orthogonal.Minus
