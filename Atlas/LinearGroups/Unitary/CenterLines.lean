import Atlas.LinearGroups.Unitary.Transvections
import Atlas.FieldTheory.FiniteQuadraticCounts

/-! Centralizers of actual unitary transvections preserve their isotropic lines.
These statements use neither transvection generation nor any group order. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

@[simp] theorem hermitian_single_left (v : Fin n → K) (i : Fin n) (b : K) :
    hermitian F K (Pi.single i b) v = b * conjugation F K (v i) := by
  classical
  simp [hermitian, Pi.single_apply]

/-- Every nonzero vector gives a surjective Hermitian pairing in the first slot. -/
theorem hermitian_left_surjective (v : Fin n → K) (hv : v ≠ 0) :
    Function.Surjective (fun x => hermitian F K x v) := by
  classical
  have hi : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hi
  have hc : conjugation F K (v i) ≠ 0 := (map_ne_zero _).mpr hi
  intro b
  refine ⟨Pi.single i (b / conjugation F K (v i)), ?_⟩
  change hermitian F K (Pi.single i (b / conjugation F K (v i))) v = b
  rw [hermitian_single_left, div_mul_cancel₀ _ hc]

/-- Commuting with a nontrivial rank-one matrix forces preservation of its
actual image line. No invertibility or isotropy assumption on the matrix is needed. -/
theorem commuting_rankOne_preserves_line (A : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (hv : v ≠ 0) (a : K) (ha : a ≠ 0)
    (hcomm : A * transvectionMatrix (F := F) v a =
      transvectionMatrix (F := F) v a * A) :
    ∃ b : K, A *ᵥ v = b • v := by
  obtain ⟨x, hx⟩ := hermitian_left_surjective (F := F) v hv a⁻¹
  change hermitian F K x v = a⁻¹ at hx
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ x) hcomm
  rw [← mulVec_mulVec, ← mulVec_mulVec, transvectionMatrix_apply,
    transvectionMatrix_apply, hx, mul_inv_cancel₀ ha, one_smul,
    mulVec_add] at h
  exact ⟨a * hermitian F K (A *ᵥ x) v, add_left_cancel h⟩

/-- Geometric span formulation of the same explicit centralizer fact. -/
theorem commuting_rankOne_mem_span (A : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (hv : v ≠ 0) (a : K) (ha : a ≠ 0)
    (hcomm : A * transvectionMatrix (F := F) v a =
      transvectionMatrix (F := F) v a * A) :
    A *ᵥ v ∈ Submodule.span K {v} := by
  obtain ⟨b, hb⟩ := commuting_rankOne_preserves_line A v hv a ha hcomm
  exact Submodule.mem_span_singleton.mpr ⟨b, hb.symm⟩

/-- A central element of the retained special unitary group preserves every
actual nonzero isotropic line, including the exceptional small-field groups. -/
theorem central_preserves_isotropic_lines (hdeg : Module.finrank F K = 2)
    (g : SU F K n hdeg) (hg : g ∈ Subgroup.center (SU F K n hdeg))
    (v : Fin n → K) (hv : v ≠ 0) (hvv : hermitian F K v v = 0) :
    ∃ b : K, g.val *ᵥ v = b • v := by
  obtain ⟨a, ha0, ha⟩ := exists_nonzero_trace_zero hdeg
  have ha' : a + conjugation F K a = 0 := ha
  apply commuting_rankOne_preserves_line (F := F) g.val v hv a ha0
  have h := Subgroup.mem_center_iff.mp hg (transvection hdeg v a hvv ha')
  exact (congrArg (fun t : SU F K n hdeg => t.val) h).symm
end Atlas.Unitary
