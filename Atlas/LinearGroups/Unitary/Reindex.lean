import Atlas.LinearGroups.Unitary.BlockEmbeddings
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Actual coordinate relabelling of SU and its genuinely generated subgroup. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n m : ℕ}

theorem hermitian_reindex (e : Fin n ≃ Fin m) (v w : Fin n → K) :
    hermitian F K (v ∘ e.symm) (w ∘ e.symm) = hermitian F K v w := by
  exact e.symm.sum_comp (fun i => v i * conjugation F K (w i))

/-- Relabel both matrix indices; the determinant and actual form are unchanged. -/
def reindexSpecialHom (hdeg : Module.finrank F K = 2) (e : Fin n ≃ Fin m) :
    SU F K n hdeg →* SU F K m hdeg where
  toFun g := ⟨Matrix.reindex e e g.val, by
    let := conjugationStarRing F K hdeg
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change (Matrix.reindex e e g.val)ᴴ * Matrix.reindex e e g.val = 1
    rw [Matrix.conjTranspose_reindex]
    change reindexRingEquiv K e g.valᴴ * reindexRingEquiv K e g.val = 1
    rw [← map_mul, show g.valᴴ * g.val = 1 from g.prop.1.1, map_one], by
      change (Matrix.reindex e e g.val).det = 1
      rw [Matrix.det_reindex_self]
      exact g.prop.2⟩
  map_one' := Subtype.ext ((reindexRingEquiv K e).map_one)
  map_mul' g h := Subtype.ext ((reindexRingEquiv K e).map_mul g.val h.val)

theorem reindexSpecialHom_transvection (hdeg : Module.finrank F K = 2)
    (e : Fin n ≃ Fin m) (v : Fin n → K) (hv : hermitian F K v v = 0)
    (a : K) (ha : a + conjugation F K a = 0) :
    reindexSpecialHom hdeg e (transvection hdeg v a hv ha) =
      transvection hdeg (v ∘ e.symm) a ((hermitian_reindex e v v).trans hv) ha := by
  apply Subtype.ext
  ext i j
  simp [reindexSpecialHom, transvection, transvectionMatrix, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.one_apply, vecMulVec]

theorem reindexSpecialHom_generated (hdeg : Module.finrank F K = 2)
    (e : Fin n ≃ Fin m) (g : SU F K n hdeg) (hg : g ∈ transvectionGenerated hdeg) :
    reindexSpecialHom hdeg e g ∈ transvectionGenerated hdeg := by
  have hle : transvectionGenerated hdeg ≤
      (transvectionGenerated hdeg).comap (reindexSpecialHom hdeg e) := by
    apply iSup_le
    intro v
    apply iSup_le
    intro hv
    intro g hg
    obtain ⟨a,rfl⟩ := hg
    change reindexSpecialHom hdeg e (transvection hdeg v a.toAdd.val hv
      ((trace_zero_iff hdeg _).mp a.toAdd.prop)) ∈ transvectionGenerated hdeg (n := m)
    rw [reindexSpecialHom_transvection]
    exact transvection_mem_generated hdeg _ _ _ _
  exact hle hg
end Atlas.Unitary
