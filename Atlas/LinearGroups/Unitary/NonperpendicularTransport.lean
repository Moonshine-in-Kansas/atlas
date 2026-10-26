import Atlas.LinearGroups.Unitary.Eichler
import Atlas.LinearGroups.Unitary.IsotropicTransport

/-! Exact transport by the full stabilizer of an isotropic vector. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

theorem normalized_isotropic_stabilizer_transport (hdeg : Module.finrank F K = 2)
    (p q r : Fin n → K) (hp : hermitian F K p p = 0)
    (hq : hermitian F K q q = 0) (hr : hermitian F K r r = 0)
    (hqp : hermitian F K q p = 1) (hrp : hermitian F K r p = 1) :
    ∃ g : SU F K n hdeg, g.val *ᵥ p = p ∧ g.val *ᵥ q = r := by
  have hpq : hermitian F K p q = 1 := by rw [← hermitian_symmetry hdeg q p, hqp, map_one]
  have hpr : hermitian F K p r = 1 := by rw [← hermitian_symmetry hdeg r p, hrp, map_one]
  let b := hermitian F K r q
  let w := r + (-1 : K) • q + (-b) • p
  have hbw : hermitian F K q r = conjugation F K b := (hermitian_symmetry hdeg r q).symm
  have hpw : hermitian F K p w = 0 := by
    simp only [w, hermitian_add_right, hermitian_smul_right, hp, hpq, hpr,
      map_neg, map_one, mul_zero, mul_one]
    ring
  have hqw : hermitian F K q w = 0 := by
    simp only [w, hermitian_add_right, hermitian_smul_right, hq, hqp, hbw,
      map_neg, map_one, mul_zero, mul_one]
    ring
  have hb : b + conjugation F K b + hermitian F K w w = 0 := by
    simp only [w, hermitian_add_left, hermitian_add_right, hermitian_smul_left,
      hermitian_smul_right, map_neg, map_one, hp, hq, hr, hpq, hqp, hpr, hrp,
      hbw, mul_zero, mul_one, zero_mul, add_zero]
    change b + conjugation F K b + _ = 0
    dsimp [b]
    ring
  let g := eichler hdeg p w b hp hpw hb
  refine ⟨g, ?_, ?_⟩
  · change eichlerMatrix (F := F) p w b *ᵥ p = p
    rw [eichlerMatrix_apply, hp, hpw]
    simp
  · change eichlerMatrix (F := F) p w b *ᵥ q = r
    rw [eichlerMatrix_apply, hqp, hqw]
    simp only [mul_one, sub_zero, one_smul]
    dsimp [w]
    module

theorem isotropic_stabilizer_transport_nonperpendicular (hdeg : Module.finrank F K = 2)
    (p q r : Fin n → K) (hp : hermitian F K p p = 0)
    (hq : hermitian F K q q = 0) (hr : hermitian F K r r = 0)
    (hqp : hermitian F K q p ≠ 0) (hrp : hermitian F K r p ≠ 0) :
    ∃ g : SU F K n hdeg, ∃ c : K, c ≠ 0 ∧ g.val *ᵥ p = p ∧ g.val *ᵥ q = c • r := by
  let a := hermitian F K q p
  let b := hermitian F K r p
  have hq' : hermitian F K (a⁻¹ • q) (a⁻¹ • q) = 0 := by
    rw [hermitian_smul_left, hermitian_smul_right, hq, mul_zero, mul_zero]
  have hr' : hermitian F K (b⁻¹ • r) (b⁻¹ • r) = 0 := by
    rw [hermitian_smul_left, hermitian_smul_right, hr, mul_zero, mul_zero]
  have hqa : hermitian F K (a⁻¹ • q) p = 1 := by
    rw [hermitian_smul_left]; exact inv_mul_cancel₀ hqp
  have hrb : hermitian F K (b⁻¹ • r) p = 1 := by
    rw [hermitian_smul_left]; exact inv_mul_cancel₀ hrp
  obtain ⟨g,hgp,hgr⟩ := normalized_isotropic_stabilizer_transport hdeg p
    (a⁻¹ • q) (b⁻¹ • r) hp hq' hr' hqa hrb
  refine ⟨g, a*b⁻¹, mul_ne_zero hqp (inv_ne_zero hrp), hgp, ?_⟩
  have h := congrArg (fun v => a • v) hgr
  rw [mulVec_smul, smul_smul, mul_inv_cancel₀ hqp, one_smul, smul_smul] at h
  exact h
end Atlas.Unitary
