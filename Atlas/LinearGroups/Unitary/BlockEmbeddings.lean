import Atlas.LinearGroups.Unitary.SpecialStabilizer
import Atlas.LinearGroups.Unitary.GeneratedNormal

/-! Actual identity-coordinate block embeddings preserve the transvection model. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

/-- The genuine inclusion on the orthogonal complement of the first norm-one vector. -/
def extendSpecialHom (hdeg : Module.finrank F K = 2) :
    SU F K n hdeg →* SU F K (n+1) hdeg :=
  (firstSpecialStabilizer (n := n) hdeg).subtype.comp
    (firstSpecialStabilizerEquiv hdeg).symm.toMonoidHom

@[simp] theorem extendSpecialHom_matrix (hdeg : Module.finrank F K = 2)
    (g : SU F K n hdeg) : (extendSpecialHom hdeg g).val = extendMatrix g.val := rfl

theorem hermitian_cons_zero (x y : Fin n → K) :
    hermitian F K (Fin.cons 0 x) (Fin.cons 0 y) = hermitian F K x y := by
  simp [hermitian, Fin.sum_univ_succ]

/-- Compatibility is proved for actual generators, not inferred from group orders. -/
theorem extendSpecialHom_transvection (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 0) (a : K)
    (ha : a + conjugation F K a = 0) :
    extendSpecialHom hdeg (transvection hdeg v a hv ha) =
      transvection hdeg (Fin.cons 0 v) a ((hermitian_cons_zero v v).trans hv) ha := by
  apply Subtype.ext
  change extendMatrix (transvectionMatrix (F := F) v a) =
    transvectionMatrix (F := F) (Fin.cons 0 v) a
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;>
    refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [extendMatrix, transvectionMatrix, vecMulVec, Matrix.one_apply, eq_comm]

/-- Every generated lower-dimensional element remains genuinely generated after extension. -/
theorem extendSpecialHom_generated (hdeg : Module.finrank F K = 2)
    (g : SU F K n hdeg) (hg : g ∈ transvectionGenerated hdeg) :
    extendSpecialHom hdeg g ∈ transvectionGenerated hdeg := by
  have hle : transvectionGenerated hdeg ≤
      (transvectionGenerated hdeg).comap (extendSpecialHom (n := n) hdeg) := by
    apply iSup_le
    intro v
    apply iSup_le
    intro hv
    intro g hg
    obtain ⟨a, rfl⟩ := hg
    change extendSpecialHom hdeg (transvection hdeg v a.toAdd.val hv
      ((trace_zero_iff hdeg _).mp a.toAdd.prop)) ∈ transvectionGenerated hdeg (n := n+1)
    rw [extendSpecialHom_transvection]
    exact transvection_mem_generated hdeg _ _ _ _
  exact hle hg

/-- Once the lower-dimensional generation theorem is proved, its full standard
stabilizer image lies in the upper-dimensional generated subgroup. -/
theorem firstSpecialStabilizer_le_generated (hdeg : Module.finrank F K = 2)
    (hgen : transvectionGenerated hdeg (n := n) = ⊤) :
    firstSpecialStabilizer (n := n) hdeg ≤ transvectionGenerated hdeg := by
  intro g hg
  let k := firstSpecialStabilizerEquiv hdeg ⟨g,hg⟩
  have hk : k ∈ transvectionGenerated hdeg := by rw [hgen]; trivial
  have h := extendSpecialHom_generated hdeg k hk
  have he : extendSpecialHom hdeg k = g := by
    exact congrArg Subtype.val ((firstSpecialStabilizerEquiv hdeg).symm_apply_apply ⟨g,hg⟩)
  rwa [he] at h
end Atlas.Unitary
