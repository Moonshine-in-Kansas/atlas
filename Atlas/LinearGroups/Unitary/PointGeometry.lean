import Atlas.LinearGroups.Unitary.NonperpendicularTransport
import Atlas.GroupTheory.PrimitivePointMoves

/-! Geometric primitivity of the actual unitary isotropic-line action. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
open scoped LinearAlgebra.Projectivization
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

def IsotropicPerp (p q : IsotropicPoints F K n) : Prop :=
  hermitian F K p.val.rep q.val.rep = 0

theorem isotropicPerp_symmetric (hdeg : Module.finrank F K = 2) :
    Symmetric (IsotropicPerp (F := F) (K := K) (n := n)) := by
  intro p q h
  change hermitian F K q.val.rep p.val.rep = 0
  rw [← hermitian_symmetry hdeg, h, map_zero]

theorem isotropicPerp_mk_right (p : IsotropicPoints F K n)
    (v : Fin n → K) (hv : v ≠ 0) (hvv : hermitian F K v v = 0) :
    IsotropicPerp p (isotropicPoint v hv hvv) ↔ hermitian F K p.val.rep v = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  change hermitian F K p.val.rep (Projectivization.mk K v hv).rep = 0 ↔ _
  rw [← ha, Units.smul_def, hermitian_smul_right]
  exact mul_eq_zero.trans (or_iff_right ((map_ne_zero _).mpr a.ne_zero))

theorem isotropicPerp_smul_right (hdeg : Module.finrank F K = 2)
    (p q : IsotropicPoints F K n) (g : SU F K n hdeg) :
    IsotropicPerp p (g • q) ↔ hermitian F K p.val.rep (g.val *ᵥ q.val.rep) = 0 := by
  have hv : g.val *ᵥ q.val.rep ≠ 0 := (smul_ne_zero_iff_ne g).mpr q.val.rep_nonzero
  have he : g • q = isotropicPoint (g.val *ᵥ q.val.rep) hv
      (su_image_isotropic hdeg g q.val.rep (isotropic_rep q)) := by
    apply Subtype.ext
    change g • q.val = Projectivization.mk K (g • q.val.rep) _
    rw [← Projectivization.smul_mk g q.val.rep_nonzero, Projectivization.mk_rep]
  rw [he, isotropicPerp_mk_right]

theorem isotropic_stabilizer_nonperpendicular_transitive (hdeg : Module.finrank F K = 2)
    (p q r : IsotropicPoints F K n) (hpq : ¬ IsotropicPerp p q) (hpr : ¬ IsotropicPerp p r) :
    ∃ g : MulAction.stabilizer (SU F K n hdeg) p, g • q = r := by
  have hqp : hermitian F K q.val.rep p.val.rep ≠ 0 :=
    fun h => hpq (isotropicPerp_symmetric hdeg h)
  have hrp : hermitian F K r.val.rep p.val.rep ≠ 0 :=
    fun h => hpr (isotropicPerp_symmetric hdeg h)
  obtain ⟨g,c,hc,hgp,hgr⟩ := isotropic_stabilizer_transport_nonperpendicular hdeg
    p.val.rep q.val.rep r.val.rep (isotropic_rep p) (isotropic_rep q) (isotropic_rep r) hqp hrp
  have hfix : g • p = p := by
    apply Subtype.ext
    change g • p.val = p.val
    rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk]
    change Projectivization.mk K (g.val *ᵥ p.val.rep) _ = _
    simp only [hgp]
  refine ⟨⟨g,hfix⟩, ?_⟩
  apply Subtype.ext
  change g • q.val = r.val
  rw [← Projectivization.mk_rep q.val, ← Projectivization.mk_rep r.val,
    Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  exact ⟨c,hgr.symm⟩

theorem isotropic_common_nonperpendicular (hdeg : Module.finrank F K = 2)
    (p q : IsotropicPoints F K n) (hpq : p ≠ q) (hperp : IsotropicPerp p q) :
    ∃ r, ¬ IsotropicPerp p r ∧ ¬ IsotropicPerp q r := by
  have hli := Projectivization.linearIndependent_pair_iff_ne.mpr
    (show p.val ≠ q.val from fun h => hpq (Subtype.ext h))
  obtain ⟨v,hv,hpv,hqv⟩ := exists_isotropic_bridge hdeg p.val.rep q.val.rep hli
    (isotropic_rep p) (isotropic_rep q) hperp
  have hv0 : v ≠ 0 := by intro he; simp [he] at hpv
  refine ⟨isotropicPoint v hv0 hv, ?_, ?_⟩ <;>
    rw [isotropicPerp_mk_right] <;> simp [hpv,hqv]

/-- An independent orthogonal isotropic pair has an isotropic dual vector for
its first member that remains perpendicular to its second member. -/
theorem exists_isotropic_dual_perpendicular (hdeg : Module.finrank F K = 2)
    (p q : Fin n → K) (hli : LinearIndependent K ![p,q])
    (hp : hermitian F K p p = 0) (hpq : hermitian F K p q = 0) :
    ∃ w, hermitian F K w w = 0 ∧ hermitian F K p w = 1 ∧ hermitian F K q w = 0 := by
  have hnot : p ∉ Submodule.span K ({q} : Set (Fin n → K)) := by
    simpa using hli.notMem_span_image (s := {1}) (x := 0) (by simp)
  obtain ⟨f,hfp,hfq⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hq0 : f q = 0 := by
    have h : f q ∈ (Submodule.span K ({q} : Set (Fin n → K))).map f :=
      Submodule.mem_map.mpr ⟨q, Submodule.subset_span (Set.mem_singleton q), rfl⟩
    simpa [hfq] using h
  obtain ⟨z,hz⟩ := hermitian_represents_dual hdeg ((f p)⁻¹ • f)
  have hpz : hermitian F K p z = 1 := by rw [hz]; simpa using inv_mul_cancel₀ hfp
  have hqz : hermitian F K q z = 0 := by rw [hz]; simp [hq0]
  obtain ⟨d,hd⟩ := hermitian_self_in_base hdeg z
  obtain ⟨a,ha⟩ := trace_surjective F K (-d)
  have htrace : a + conjugation F K a = -hermitian F K z z := by
    rw [← trace_formula hdeg, ha, map_neg, hd]
  have hzp : hermitian F K z p = 1 := by rw [← hermitian_symmetry hdeg p z, hpz, map_one]
  have hqp : hermitian F K q p = 0 := by rw [← hermitian_symmetry hdeg p q, hpq, map_zero]
  refine ⟨z + a • p, ?_, ?_, ?_⟩
  · simp only [hermitian_add_left, hermitian_add_right, hermitian_smul_left,
      hermitian_smul_right, hp, hpz, hzp, mul_zero, mul_one, add_zero]
    linear_combination htrace
  · rw [hermitian_add_right, hermitian_smul_right, hp, mul_zero, add_zero, hpz]
  · rw [hermitian_add_right, hermitian_smul_right, hqp, mul_zero, add_zero, hqz]

/-- A concrete transvection in the second stabilizer breaks the first
orthogonality relation. This is the geometric ingredient that rules out blocks. -/
theorem isotropic_stabilizer_break_perpendicular (hdeg : Module.finrank F K = 2)
    (p q : IsotropicPoints F K n) (hpq : p ≠ q) (hperp : IsotropicPerp p q) :
    ∃ g : MulAction.stabilizer (SU F K n hdeg) q, ¬ IsotropicPerp p (g • p) := by
  have hli := Projectivization.linearIndependent_pair_iff_ne.mpr
    (show p.val ≠ q.val from fun h => hpq (Subtype.ext h))
  obtain ⟨w,hw,hpw,hqw⟩ := exists_isotropic_dual_perpendicular hdeg
    p.val.rep q.val.rep hli (isotropic_rep p) hperp
  obtain ⟨t,ht,htrace⟩ := exists_nonzero_trace_zero hdeg
  have ht0 : t + conjugation F K t = 0 := htrace
  let g := transvection hdeg w t hw ht0
  have hgq : g.val *ᵥ q.val.rep = q.val.rep := by
    change transvectionMatrix (F := F) w t *ᵥ q.val.rep = _
    rw [transvectionMatrix_apply, hqw, mul_zero, zero_smul, add_zero]
  have hfix : g • q = q := by
    apply Subtype.ext
    change g • q.val = q.val
    rw [← Projectivization.mk_rep q.val, Projectivization.smul_mk]
    change Projectivization.mk K (g.val *ᵥ q.val.rep) _ = _
    simp only [hgq]
  refine ⟨⟨g,hfix⟩, ?_⟩
  change ¬ IsotropicPerp p (g • p)
  rw [isotropicPerp_smul_right]
  change hermitian F K p.val.rep (transvectionMatrix (F := F) w t *ᵥ p.val.rep) ≠ 0
  rw [transvectionMatrix_apply, hpw, mul_one, hermitian_add_right,
    hermitian_smul_right, isotropic_rep, hpw, mul_one, zero_add]
  exact (map_ne_zero _).mpr ht

/-- Primitivity holds even in the small nonsimple cases. No order, generation or
simplicity theorem is used; the stabilizer moves are actual matrices. -/
theorem special_isotropic_preprimitive (hdeg : Module.finrank F K = 2)
    (p : IsotropicPoints F K n) :
    MulAction.IsPreprimitive (SU F K n hdeg) (IsotropicPoints F K n) :=
  Atlas.GroupTheory.primitive_of_nonrelated_orbit_and_moves p IsotropicPerp
    (isotropicPerp_symmetric hdeg) (isotropic_stabilizer_nonperpendicular_transitive hdeg)
    (isotropic_common_nonperpendicular hdeg) (isotropic_stabilizer_break_perpendicular hdeg)

theorem projective_isotropic_preprimitive (hdeg : Module.finrank F K = 2)
    (hn : 0 < n) (p : IsotropicPoints F K n) :
    letI := isotropicAction hdeg hn
    MulAction.IsPreprimitive (PSU F K n hdeg) (IsotropicPoints F K n) := by
  letI := isotropicAction hdeg hn
  letI := special_isotropic_preprimitive hdeg p
  let f : IsotropicPoints F K n →ₑ[projection F K n hdeg] IsotropicPoints F K n :=
    { toFun := id, map_smul' := fun _ _ => rfl }
  exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id
end Atlas.Unitary
