import Atlas.LinearGroups.Triality.TorusAction
import Atlas.LinearGroups.Triality.WeylRelations
import Atlas.LinearGroups.Triality.WeylRootData

/-! Conjugation of the actual diagonal torus by the two relative Weyl lifts. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def shortTorusReflection (h : Kˣ × Fˣ) : Kˣ × Fˣ :=
  (baseUnit F K h.2 / h.1, h.2)

def longTorusReflection (h : Kˣ × Fˣ) : Kˣ × Fˣ :=
  (h.1, normUnit F K h.1 / h.2)

set_option maxHeartbeats 2500000 in
-- Expand the eight coordinate identities for diagonal conjugation.
theorem shortWeyl_torus_intertwine (hdeg : Module.finrank F K = 3) (h : Kˣ × Fˣ) :
    shortWeyl F K * torusMap F K h =
      torusMap F K (shortTorusReflection F K h) * shortWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [Subgroup.coe_mul, LinearEquiv.mul_apply, shortWeyl_apply,
      torusMap, torusWeights, diagonalEmbedding, diagonalLinear, shortTorusReflection,
      sigmaUnit, baseUnit, FiniteCubic.sigma_cube hdeg] <;>
    field_simp <;> simp

set_option maxHeartbeats 2500000 in
-- Expand the eight coordinate identities for diagonal conjugation.
theorem longWeyl_torus_intertwine (hdeg : Module.finrank F K = 3) (h : Kˣ × Fˣ) :
    longWeyl F K * torusMap F K h =
      torusMap F K (longTorusReflection F K h) * longWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [Subgroup.coe_mul, LinearEquiv.mul_apply, longWeyl_apply,
      torusMap, torusWeights, diagonalEmbedding, diagonalLinear, longTorusReflection,
      sigmaUnit, baseUnit, normUnit, FiniteCubic.norm_formula hdeg] <;>
    field_simp <;> simp

theorem shortWeyl_normalizes_torus (hdeg : Module.finrank F K = 3) :
    shortWeyl F K ∈ Subgroup.normalizer (torus F K : Set (O_DPlus 4 K)) := by
  apply Subgroup.mem_normalizer_fintype
  intro g hg
  obtain ⟨h, rfl⟩ := hg
  refine ⟨shortTorusReflection F K h, ?_⟩
  rw [shortWeyl_torus_intertwine F K hdeg, mul_assoc, mul_inv_cancel, mul_one]

theorem longWeyl_normalizes_torus (hdeg : Module.finrank F K = 3) :
    longWeyl F K ∈ Subgroup.normalizer (torus F K : Set (O_DPlus 4 K)) := by
  apply Subgroup.mem_normalizer_fintype
  intro g hg
  obtain ⟨h, rfl⟩ := hg
  refine ⟨longTorusReflection F K h, ?_⟩
  rw [longWeyl_torus_intertwine F K hdeg, mul_assoc, mul_inv_cancel, mul_one]

/-- Literal products of the two previously constructed rank-one representatives. -/
def weylLift (w : Fin 12) : O_DPlus 4 K :=
  ((weylWord w).map fun s => if s then shortWeyl F K else longWeyl F K).prod

theorem weylLift_mem (w : Fin 12) : weylLift F K w ∈ generated F K := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
  cases s
  · exact longWeyl_mem F K
  · exact shortWeyl_mem F K

theorem weylLift_normalizes_torus (hdeg : Module.finrank F K = 3) (w : Fin 12) :
    weylLift F K w ∈ Subgroup.normalizer (torus F K : Set (O_DPlus 4 K)) := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
  cases s
  · exact longWeyl_normalizes_torus F K hdeg
  · exact shortWeyl_normalizes_torus F K hdeg

end Atlas.Triality

