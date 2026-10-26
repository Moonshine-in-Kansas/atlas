import Atlas.LinearGroups.Unitary.GeneratedNormal

/-! # Normal closure of one isotropic line group

This identifies the actual normal closure with the transvection-generated
subgroup. It does not assume or assert that the latter is all of SU.
-/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
open scoped LinearAlgebra.Projectivization
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

theorem lineTransvections_eq_of_projective_eq (hdeg : Module.finrank F K = 2)
    (v w : Fin n → K) (hv : hermitian F K v v = 0) (hw : hermitian F K w w = 0)
    (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (he : Projectivization.mk K v hv0 = Projectivization.mk K w hw0) :
    lineTransvections hdeg v hv = lineTransvections hdeg w hw := by
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K v w hv0 hw0).mp he
  have hc0 : c ≠ 0 := by
    intro h
    apply hv0
    rw [← hc, h, zero_smul]
  subst v
  exact lineTransvections_smul hdeg w hw c hc0 hv

theorem lineTransvections_map_conj (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 0) (g : SU F K n hdeg) :
    (lineTransvections hdeg v hv).map (MulAut.conj g).toMonoidHom =
      lineTransvections hdeg (g.val *ᵥ v) (su_image_isotropic hdeg g v hv) := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    change transvection hdeg (g.val *ᵥ v) a.toAdd.val (su_image_isotropic hdeg g v hv)
      ((trace_zero_iff hdeg _).mp a.toAdd.prop) =
      g * transvection hdeg v a.toAdd.val hv ((trace_zero_iff hdeg _).mp a.toAdd.prop) * g⁻¹
    exact (transvection_conjugate hdeg g v a.toAdd.val hv ((trace_zero_iff hdeg _).mp a.toAdd.prop)).symm
  · rintro ⟨a, rfl⟩
    refine ⟨lineTransvectionHom hdeg v hv a, ⟨a, rfl⟩, ?_⟩
    exact transvection_conjugate hdeg g v a.toAdd.val hv ((trace_zero_iff hdeg _).mp a.toAdd.prop)

theorem pointTransvections_map_conj (hdeg : Module.finrank F K = 2)
    (p : IsotropicPoints F K n) (g : SU F K n hdeg) :
    (pointTransvections hdeg p).map (MulAut.conj g).toMonoidHom =
      pointTransvections hdeg (g • p) := by
  rw [pointTransvections, lineTransvections_map_conj]
  have hv0 : g.val *ᵥ p.val.rep ≠ 0 :=
    (smul_ne_zero_iff_ne g).mpr p.val.rep_nonzero
  apply lineTransvections_eq_of_projective_eq hdeg _ _ _ _ hv0 (g • p).val.rep_nonzero
  rw [Projectivization.mk_rep]
  change Projectivization.mk K (g • p.val.rep) _ = g • p.val
  rw [← Projectivization.smul_mk g p.val.rep_nonzero, Projectivization.mk_rep]

theorem pointTransvections_le_generated (hdeg : Module.finrank F K = 2)
    (p : IsotropicPoints F K n) : pointTransvections hdeg p ≤ transvectionGenerated hdeg :=
  le_iSup_of_le p.val.rep (le_iSup_of_le (isotropic_rep p) le_rfl)

theorem transvectionGenerated_eq_iSup_points (hdeg : Module.finrank F K = 2) :
    transvectionGenerated hdeg (n := n) = ⨆ p : IsotropicPoints F K n, pointTransvections hdeg p := by
  apply le_antisymm
  · apply iSup_le
    intro v
    apply iSup_le
    intro hv
    by_cases hv0 : v = 0
    · subst v
      rintro x ⟨a, rfl⟩
      have he : lineTransvectionHom hdeg (0 : Fin n → K) hv a = 1 := by
        apply Subtype.ext
        simp [lineTransvectionHom, transvection, transvectionMatrix, Matrix.vecMulVec]
        rfl
      rw [he]
      exact Subgroup.one_mem _
    · let p := isotropicPoint v hv0 hv
      have he : lineTransvections hdeg v hv = pointTransvections hdeg p := by
        apply lineTransvections_eq_of_projective_eq hdeg _ _ _ _ hv0 p.val.rep_nonzero
        exact (Projectivization.mk_rep p.val).symm
      rw [he]
      exact le_iSup (fun p : IsotropicPoints F K n => pointTransvections hdeg p) p
  · exact iSup_le (pointTransvections_le_generated hdeg)

theorem normalClosure_pointTransvections (hdeg : Module.finrank F K = 2)
    (p : IsotropicPoints F K n) :
    Subgroup.normalClosure (pointTransvections hdeg p : Set (SU F K n hdeg)) =
      transvectionGenerated hdeg := by
  apply le_antisymm
  · exact Subgroup.normalClosure_le_normal (pointTransvections_le_generated hdeg p)
  · rw [transvectionGenerated_eq_iSup_points]
    apply iSup_le
    intro q
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (SU F K n hdeg) p q
    rw [← pointTransvections_map_conj]
    rintro x ⟨a, ha, rfl⟩
    exact Subgroup.Normal.conj_mem
      (inferInstance : (Subgroup.normalClosure (pointTransvections hdeg p : Set (SU F K n hdeg))).Normal)
      a (Subgroup.subset_normalClosure ha) g
end Atlas.Unitary
