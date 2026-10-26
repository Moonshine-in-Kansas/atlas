import Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge
import Atlas.LinearGroups.Orthogonal.D3ExteriorKernel

/-! The Hodge fixed space spans the full exterior square over the quadratic field. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic Atlas.Orthogonal.B2Exterior Matrix
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem hodge_symmetrize_mem (hdeg : Module.finrank F K = 2) (v : Six K) :
    v + hodge (F := F) v ∈ hodgeFixed hdeg := by
  change hodge (F := F) (v + hodge (F := F) v) = v + hodge (F := F) v
  rw [hodge_add,hodge_involutive hdeg v,add_comm]

/-- Equality on the actual fixed vectors determines any K-linear map, including in characteristic two. -/
theorem hodgeFixed_linear_ext (hdeg : Module.finrank F K = 2)
    {W : Type*} [AddCommGroup W] [Module K W]
    (L M : Six K →ₗ[K] W)
    (h : ∀ v : hodgeFixed hdeg, L v.val = M v.val) : L = M := by
  obtain ⟨a,ha⟩ : ∃ a : K, conjugation F K a ≠ a := by
    by_contra! hfix
    apply conjugation_ne_one hdeg
    ext a
    exact hfix a
  let D := L-M
  have hD (v : hodgeFixed hdeg) : D v.val = 0 := sub_eq_zero.mpr (h v)
  apply LinearMap.ext
  intro v
  have h1 := hD ⟨v+hodge (F := F) v,hodge_symmetrize_mem hdeg v⟩
  change D (v+hodge (F := F) v) = 0 at h1
  rw [map_add] at h1
  have hj : D (hodge (F := F) v) = -D v := eq_neg_of_add_eq_zero_right h1
  have h2 := hD ⟨a • v+hodge (F := F) (a • v),hodge_symmetrize_mem hdeg (a • v)⟩
  change D (a • v+hodge (F := F) (a • v)) = 0 at h2
  rw [hodge_smul,map_add,map_smul,map_smul,hj,smul_neg,← sub_eq_add_neg,← sub_smul] at h2
  have hz : D v = 0 := (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm ha))
  exact sub_eq_zero.mp hz

theorem exteriorMap_scalar_of_hodgeFixed (hdeg : Module.finrank F K = 2)
    (A : Matrix (Fin 4) (Fin 4) K) (c : F)
    (h : ∀ v : hodgeFixed hdeg, exteriorMap A v.val = c • v.val) :
    ∀ w : Six K, exteriorMap A w = algebraMap F K c • w := by
  have he : exteriorMap A = (algebraMap F K c) • (LinearMap.id : Six K →ₗ[K] Six K) := by
    apply hodgeFixed_linear_ext hdeg
    intro v
    change exteriorMap A v.val = (algebraMap F K c) • v.val
    rw [h v]
    ext i
    exact Algebra.smul_def c (v.val i)
  intro w
  exact LinearMap.congr_fun he w

theorem matrix_scalar_of_hodgeFixed_scalar (hdeg : Module.finrank F K = 2)
    (A : Matrix (Fin 4) (Fin 4) K) (c : F) (hc : c ≠ 0)
    (h : ∀ v : hodgeFixed hdeg, exteriorMap A v.val = c • v.val) :
    ∃ a : K, a^2 = algebraMap F K c ∧ A = a • 1 :=
  D3Exterior.scalar_of_exteriorMap_scalar A (algebraMap F K c)
    ((map_ne_zero _).mpr hc) (exteriorMap_scalar_of_hodgeFixed hdeg A c h)

end Atlas.Orthogonal.Minus
