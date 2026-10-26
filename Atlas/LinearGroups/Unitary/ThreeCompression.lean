import Atlas.LinearGroups.Unitary.SpecialTransport
import Atlas.LinearGroups.Unitary.IsotropicTransport
import Atlas.LinearGroups.Unitary.WittPair

/-! Compression of an actual three-coordinate vector by an actual SU₃ matrix.
The isotropic case is included, so a vanishing triple norm is never discarded. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
open scoped LinearAlgebra.Projectivization
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Nonzero Hermitian norm can be scaled to one using the proved norm map. -/
theorem exists_normalizing_scalar {n : ℕ} (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ hermitian F K (c • v) (c • v) = 1 := by
  obtain ⟨s, hs⟩ := hermitian_self_in_base hdeg v
  obtain ⟨a, ha⟩ := norm_surjective F K s
  have hnorm : a * conjugation F K a = hermitian F K v v := by
    rw [← norm_formula hdeg, ha, hs]
  have ha0 : a ≠ 0 := by intro he; simp [he] at hnorm; exact hv hnorm.symm
  have hba : conjugation F K a ≠ 0 := (map_ne_zero _).mpr ha0
  refine ⟨a⁻¹, inv_ne_zero ha0, ?_⟩
  rw [hermitian_smul_left, hermitian_smul_right, map_inv₀, ← hnorm]
  field_simp

/-- Every three-coordinate vector can be moved into a coordinate plane, whether
its restricted norm is nonzero or isotropic. -/
theorem exists_special_compress_three (hdeg : Module.finrank F K = 2) (v : Fin 3 → K) :
    ∃ g : SU F K 3 hdeg, (g.val *ᵥ v) 2 = 0 := by
  by_cases hv0 : v = 0
  · exact ⟨1, by simp [hv0]⟩
  by_cases hvv : hermitian F K v v = 0
  · obtain ⟨a,b,ha,hb⟩ := exists_witt_parameters hdeg
    let w : Fin 3 → K := ![1,a,0]
    have hw : w ≠ 0 := by intro h; have := congrFun h 0; simp [w] at this
    have hww : hermitian F K w w = 0 := by
      simp [w, hermitian, Fin.sum_univ_succ, ha]
    let p := isotropicPoint v hv0 hvv
    let q := isotropicPoint w hw hww
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SU F K 3 hdeg) p q
    have he := congrArg Subtype.val hg
    change g • Projectivization.mk K v hv0 = Projectivization.mk K w hw at he
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at he
    obtain ⟨c,hc⟩ := he
    refine ⟨g, ?_⟩
    change (g • v) 2 = 0
    rw [← hc]
    simp [w]
  · obtain ⟨c,hc,hcv⟩ := exists_normalizing_scalar hdeg v hvv
    obtain ⟨g,hg⟩ := exists_special_unitary_map hdeg (by decide : 2 ≤ 3)
      (c • v) (Pi.single 0 1) hcv (by simp)
    refine ⟨g, ?_⟩
    rw [mulVec_smul] at hg
    have h := congrFun hg 2
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, show (2 : Fin 3) ≠ 0 by decide,
      if_false] at h
    exact (mul_eq_zero.mp h).resolve_left hc
end Atlas.Unitary
