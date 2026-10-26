import Atlas.LinearGroups.Unitary.ThreeCompression
import Atlas.LinearGroups.Unitary.IsotropicTransport
import Atlas.LinearGroups.Unitary.WittPair

/-! Compression of an actual four-coordinate vector by an actual SU₄ matrix.
The isotropic case is included, so a vanishing four-coordinate norm is never discarded. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
open scoped LinearAlgebra.Projectivization
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Every four-coordinate vector can be moved into a three-coordinate subspace, whether
its restricted norm is nonzero or isotropic. -/
theorem exists_special_compress_four (hdeg : Module.finrank F K = 2) (v : Fin 4 → K) :
    ∃ g : SU F K 4 hdeg, (g.val *ᵥ v) 3 = 0 := by
  by_cases hv0 : v = 0
  · exact ⟨1, by simp [hv0]⟩
  by_cases hvv : hermitian F K v v = 0
  · obtain ⟨a,b,ha,hb⟩ := exists_witt_parameters hdeg
    let w : Fin 4 → K := ![1,a,0,0]
    have hw : w ≠ 0 := by intro h; have := congrFun h 0; simp [w] at this
    have hww : hermitian F K w w = 0 := by
      simp [w, hermitian, Fin.sum_univ_succ, ha]
    let p := isotropicPoint v hv0 hvv
    let q := isotropicPoint w hw hww
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SU F K 4 hdeg) p q
    have he := congrArg Subtype.val hg
    change g • Projectivization.mk K v hv0 = Projectivization.mk K w hw at he
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at he
    obtain ⟨c,hc⟩ := he
    refine ⟨g, ?_⟩
    change (g • v) 3 = 0
    rw [← hc]
    simp [w]
  · obtain ⟨c,hc,hcv⟩ := exists_normalizing_scalar hdeg v hvv
    obtain ⟨g,hg⟩ := exists_special_unitary_map hdeg (by decide : 2 ≤ 4)
      (c • v) (Pi.single 0 1) hcv (by simp)
    refine ⟨g, ?_⟩
    rw [mulVec_smul] at hg
    have h := congrFun hg 3
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, show (3 : Fin 4) ≠ 0 by decide,
      if_false] at h
    exact (mul_eq_zero.mp h).resolve_left hc
end Atlas.Unitary
