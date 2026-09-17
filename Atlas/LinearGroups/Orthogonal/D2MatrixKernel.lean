import Atlas.LinearGroups.Orthogonal.D2MatrixAction

namespace Atlas.Orthogonal.D2Matrix
open Matrix
variable {F : Type*} [Field F]

theorem toOrthogonal_eq_one_iff (g : PairSL (F := F)) :
    toOrthogonal g = 1 ↔ ∀ M : Mat (F := F), g.1.val*M*g.2⁻¹.val = M := by
  constructor
  · intro hg M
    have h := toOrthogonal_coordinates g (coordinates.symm M)
    rw [hg] at h
    change coordinates (coordinates.symm M) = g.1.val*coordinates (coordinates.symm M)*g.2⁻¹.val at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · intro hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply coordinates.injective
    exact (toOrthogonal_coordinates g v).trans (hg (coordinates v))

/-- The full action kernel is exactly the diagonal copy of the scalar SL2 center. -/
theorem toOrthogonal_kernel_iff (g : PairSL (F := F)) :
    toOrthogonal g = 1 ↔ g.1 = g.2 ∧ g.1 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  rw [toOrthogonal_eq_one_iff]
  constructor
  · intro hg
    have hid := hg 1
    rw [mul_one] at hid
    have heq : g.1 = g.2 := by
      apply Subtype.ext
      have ht := congrArg (fun M : Mat (F := F) => M*g.2.val) hid
      rw [mul_assoc,← SpecialLinearGroup.coe_mul g.2⁻¹ g.2,inv_mul_cancel,SpecialLinearGroup.coe_one,
        mul_one,one_mul] at ht
      exact ht
    refine ⟨heq, ?_⟩
    rw [Subgroup.mem_center_iff]
    intro B
    apply Subtype.ext
    have ht := congrArg (fun M : Mat (F := F) => M*g.2.val) (hg B.val)
    rw [mul_assoc,← SpecialLinearGroup.coe_mul g.2⁻¹ g.2,inv_mul_cancel,SpecialLinearGroup.coe_one,
      mul_one,← heq] at ht
    exact ht.symm
  · rintro ⟨heq,hcenter⟩ M
    obtain ⟨a,ha,hscalar⟩ := SpecialLinearGroup.mem_center_iff.mp hcenter
    have hcomm : g.1.val*M = M*g.1.val := by
      rw [← hscalar]
      exact (Matrix.scalar_commute a (Commute.all a) M).eq
    rw [hcomm,heq,mul_assoc,← SpecialLinearGroup.coe_mul,mul_inv_cancel,
      SpecialLinearGroup.coe_one,mul_one]

/-- Explicit scalar form of the structural kernel, valid over every field. -/
theorem toOrthogonal_kernel_scalar (g : PairSL (F := F)) :
    toOrthogonal g = 1 ↔ ∃ a : F, a^2 = 1 ∧
      Matrix.scalar (Fin 2) a = g.1.val ∧ Matrix.scalar (Fin 2) a = g.2.val := by
  rw [toOrthogonal_kernel_iff]
  constructor
  · rintro ⟨heq,hcenter⟩
    obtain ⟨a,ha,hs⟩ := SpecialLinearGroup.mem_center_iff.mp hcenter
    exact ⟨a,by simpa using ha,hs,heq ▸ hs⟩
  · rintro ⟨a,ha,h1,h2⟩
    refine ⟨Subtype.ext (h1.symm.trans h2), ?_⟩
    exact SpecialLinearGroup.mem_center_iff.mpr ⟨a,by simpa using ha,h1⟩
end Atlas.Orthogonal.D2Matrix

namespace Atlas.Orthogonal.D2Matrix
open Matrix
variable {F : Type*} [Field F]

/-- Scalar action on all determinant coordinates forces both SL2 factors to be central. -/
theorem matrixAction_scalar_implies_centers (g : PairSL (F := F)) (c : F) (hc : c ≠ 0)
    (h : ∀ M : Mat (F := F), g.1.val*M*g.2⁻¹.val = c • M) :
    g.1 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ∧
      g.2 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  have hAB : g.1.val = c • g.2.val := by
    have ht := congrArg (fun M : Mat (F := F) => M*g.2.val) (h 1)
    rw [mul_one,mul_assoc,← SpecialLinearGroup.coe_mul g.2⁻¹ g.2,
      inv_mul_cancel,SpecialLinearGroup.coe_one,mul_one,smul_mul_assoc,one_mul] at ht
    exact ht
  have hcommB (M : Mat (F := F)) : g.2.val*M = M*g.2.val := by
    have ht := congrArg (fun N : Mat (F := F) => N*g.2.val) (h M)
    rw [mul_assoc,← SpecialLinearGroup.coe_mul g.2⁻¹ g.2,
      inv_mul_cancel,SpecialLinearGroup.coe_one,mul_one,hAB,smul_mul_assoc,smul_mul_assoc] at ht
    exact (smul_right_injective _ hc) ht
  constructor
  · rw [Subgroup.mem_center_iff]
    intro B
    apply Subtype.ext
    change B.val*g.1.val = g.1.val*B.val
    rw [hAB,smul_mul_assoc,mul_smul_comm,hcommB]
  · rw [Subgroup.mem_center_iff]
    intro B
    apply Subtype.ext
    exact (hcommB B.val).symm

/-- The actual projective action kernel forces scalar matrices in both factors. -/
theorem toOrthogonal_scalar_implies_centers (g : PairSL (F := F)) (c : F) (hc : c ≠ 0)
    (h : ∀ v : VectorD 2 F, (toOrthogonal g).val v = c • v) :
    g.1 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ∧
      g.2 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  apply matrixAction_scalar_implies_centers g c hc
  intro M
  have ht := toOrthogonal_coordinates g (coordinates.symm M)
  rw [h,map_smul,LinearEquiv.apply_symm_apply] at ht
  exact ht.symm
end Atlas.Orthogonal.D2Matrix

namespace Atlas.Orthogonal.D2Matrix
open Matrix
variable {F : Type*} [Field F]

private theorem SL2_center_inv_eq_self (B : SpecialLinearGroup (Fin 2) F)
    (hB : B ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) : B⁻¹ = B := by
  obtain ⟨b,hb,hs⟩ := SpecialLinearGroup.mem_center_iff.mp hB
  have hb' : b^2 = 1 := by simpa using hb
  have hh : B*B = 1 := by
    apply Subtype.ext
    rw [SpecialLinearGroup.coe_mul,← hs,← map_mul,← pow_two,hb',map_one]
    rfl
  exact inv_eq_of_mul_eq_one_right hh

/-- The full preimage of ambient scalar isometries is the product of the two SL2 centers. -/
theorem toOrthogonal_scalar_iff_centers (g : PairSL (F := F)) :
    (∃ c : F, c^2 = 1 ∧ ∀ v : VectorD 2 F, (toOrthogonal g).val v = c • v) ↔
      g.1 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ∧
      g.2 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  constructor
  · rintro ⟨c,hc,h⟩
    apply toOrthogonal_scalar_implies_centers g c _ h
    intro hz
    rw [hz,zero_pow (by decide : 2 ≠ 0)] at hc
    exact zero_ne_one hc
  · rintro ⟨hA,hB⟩
    obtain ⟨a,ha,hsa⟩ := SpecialLinearGroup.mem_center_iff.mp hA
    obtain ⟨b,hb,hsb⟩ := SpecialLinearGroup.mem_center_iff.mp hB
    have ha' : a^2 = 1 := by simpa using ha
    have hb' : b^2 = 1 := by simpa using hb
    refine ⟨a*b,by rw [mul_pow,ha',hb',mul_one],?_⟩
    intro v
    apply coordinates.injective
    rw [toOrthogonal_coordinates,map_smul,SL2_center_inv_eq_self g.2 hB,← hsa,← hsb]
    ext i j
    simp [Matrix.scalar,Matrix.diagonal_mul,Matrix.mul_diagonal,Pi.smul_apply,smul_eq_mul]
    ring
end Atlas.Orthogonal.D2Matrix
