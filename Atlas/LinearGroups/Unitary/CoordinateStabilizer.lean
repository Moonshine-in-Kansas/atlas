import Atlas.LinearGroups.Unitary.IsotropicAction
import Mathlib.Algebra.Pointwise.Stabilizer

/-! Stabilizer of the actual coordinate projective frame, for detecting the
binary dimension-three transvection-generation exception. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
open scoped LinearAlgebra.Projectivization Pointwise
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

def coordinatePoint (i : Fin n) : ℙ K (Fin n → K) :=
  Projectivization.mk K (Pi.single i 1) (by simp)

def coordinateFrame : Set (ℙ K (Fin n → K)) := Set.range (coordinatePoint (K := K))

def coordinateStabilizer (hdeg : Module.finrank F K = 2) (n : ℕ) : Subgroup (SU F K n hdeg) :=
  MulAction.stabilizer (SU F K n hdeg) (coordinateFrame (K := K) (n := n))

theorem coordinateStabilizer_mem_of_columns (hdeg : Module.finrank F K = 2)
    (g : SU F K n hdeg)
    (hg : ∀ i : Fin n, ∃ j : Fin n, ∃ c : K, c ≠ 0 ∧ g.val *ᵥ Pi.single i 1 = c • Pi.single j 1) :
    g ∈ coordinateStabilizer hdeg n := by
  apply (MulAction.mem_stabilizer_set_iff_smul_set_subset (Set.finite_range _)).mpr
  rintro p ⟨q,⟨i,rfl⟩,rfl⟩
  obtain ⟨j,c,hc,h⟩ := hg i
  refine ⟨j, ?_⟩
  change coordinatePoint j = g • coordinatePoint i
  symm
  rw [coordinatePoint, coordinatePoint, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff']
  exact ⟨c,h.symm⟩

theorem coordinateStabilizer_columns (hdeg : Module.finrank F K = 2)
    (g : SU F K n hdeg) (hg : g ∈ coordinateStabilizer hdeg n) (i : Fin n) :
    ∃ j : Fin n, ∃ c : K, g.val *ᵥ Pi.single i 1 = c • Pi.single j 1 := by
  have h := (MulAction.mem_stabilizer_set_iff_smul_set_subset (Set.finite_range _)).mp hg
  obtain ⟨j,hj⟩ := h (Set.smul_mem_smul_set (show coordinatePoint i ∈ coordinateFrame from ⟨i,rfl⟩))
  change coordinatePoint j = g • coordinatePoint i at hj
  rw [coordinatePoint, coordinatePoint, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff'] at hj
  obtain ⟨c,hc⟩ := hj
  have hc0 : c ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at hc
    have : (Pi.single j 1 : Fin n → K) ≠ 0 := by simp
    exact this hc.symm
  refine ⟨j,c⁻¹, ?_⟩
  have he := congrArg (fun v => c⁻¹ • v) hc
  change g • (Pi.single i 1 : Fin n → K) = _
  simpa only [smul_smul, inv_mul_cancel₀ hc0, one_smul] using he

theorem center_le_coordinateStabilizer (hdeg : Module.finrank F K = 2) (hn : 0 < n) :
    Subgroup.center (SU F K n hdeg) ≤ coordinateStabilizer hdeg n := by
  intro g hg
  obtain ⟨c,hc⟩ := central_matrix_scalar hdeg hn g hg
  have hc0 : c ≠ 0 := by
    intro h
    have he := g.prop.2
    rw [hc,h] at he
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    simpa using he
  apply coordinateStabilizer_mem_of_columns hdeg g
  intro i
  refine ⟨i,c,hc0, ?_⟩
  rw [hc]
  ext j
  simp [Matrix.mulVec_diagonal]
end Atlas.Unitary
