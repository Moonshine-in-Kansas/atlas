import Atlas.LinearGroups.Orthogonal.RootSubgroup

/-! # Independence of singular-line representative and full line-stabilizer normalization -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (u : V) (hu : Q u = 0)

/-- Rescaling the singular direction does not enlarge its actual subgroup. -/
theorem rootSubgroup_scale_le (c : F) (hc : c ≠ 0) :
    rootSubgroup Q (c • u) (by rw [Q.map_smul, hu, smul_zero]) ≤ rootSubgroup Q u hu := by
  rintro g ⟨v, rfl⟩
  have hv : Q.polarBilin u v.toAdd.val = 0 := by
    have h := v.toAdd.prop
    change Q.polarBilin (c • u) v.toAdd.val = 0 at h
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  have hcv : Q.polarBilin u (c • v.toAdd.val) = 0 := by rw [map_smul, hv, smul_zero]
  refine ⟨Multiplicative.ofAdd ⟨c • v.toAdd.val, hcv⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact (siegel_scale Q u v.toAdd.val x c).symm

/-- The subgroup depends on the singular line, not its nonzero representative. -/
theorem rootSubgroup_scale (c : F) (hc : c ≠ 0) :
    rootSubgroup Q (c • u) (by rw [Q.map_smul, hu, smul_zero]) = rootSubgroup Q u hu := by
  apply le_antisymm (rootSubgroup_scale_le Q u hu c hc)
  have h := rootSubgroup_scale_le Q (c • u) (by rw [Q.map_smul, hu, smul_zero]) c⁻¹ (inv_ne_zero hc)
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h

/-- Full isometries conjugate the actual local subgroup to that of the image line. -/
theorem rootSubgroup_conj (g : isometrySubgroup Q) :
    (rootSubgroup Q u hu).map (MulAut.conj g) =
      rootSubgroup Q (g.val u) ((isometryCarrierEquiv Q g).map_app u |>.trans hu) := by
  ext x
  constructor
  · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
    have hv := isometry_polar Q (isometryCarrierEquiv Q g) u v.toAdd.val
    have hp : Q.polarBilin (g.val u) (g.val v.toAdd.val) = 0 := hv.trans v.toAdd.prop
    refine ⟨Multiplicative.ofAdd ⟨g.val v.toAdd.val, hp⟩, ?_⟩
    exact (siegelElement_conj Q g u v.toAdd.val hu v.toAdd.prop).symm
  · rintro ⟨v, rfl⟩
    have hp : Q.polarBilin u (g.val.symm v.toAdd.val) = 0 := by
      have h := isometry_polar Q (isometryCarrierEquiv Q g) u (g.val.symm v.toAdd.val)
      change Q.polarBilin (g.val u) (g.val (g.val.symm v.toAdd.val)) =
        Q.polarBilin u (g.val.symm v.toAdd.val) at h
      rw [g.val.apply_symm_apply] at h
      exact h.symm.trans v.toAdd.prop
    let w : Multiplicative (rootParameterSpace Q u) :=
      Multiplicative.ofAdd ⟨g.val.symm v.toAdd.val, hp⟩
    refine ⟨rootParameterHom Q u hu w, ⟨w, rfl⟩, ?_⟩
    change g * siegelElement Q u (g.val.symm v.toAdd.val) hu hp * g⁻¹ = _
    rw [siegelElement_conj]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    change siegel Q (g.val u) (g.val (g.val.symm v.toAdd.val)) z =
      siegel Q (g.val u) v.toAdd.val z
    rw [g.val.apply_symm_apply]

/-- Every element stabilizing the singular line normalizes its abelian subgroup. -/
theorem line_stabilizer_normalizes_root (g : isometrySubgroup Q) (c : F) (hc : c ≠ 0)
    (hg : g.val u = c • u) : g ∈ Subgroup.normalizer (rootSubgroup Q u hu : Set (isometrySubgroup Q)) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [rootSubgroup_conj]
  simpa only [hg] using rootSubgroup_scale Q u hu c hc

end Atlas.Orthogonal
