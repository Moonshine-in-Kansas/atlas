/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ATLAS contributors
-/
import Atlas.LinearGroups.Elementary
import Atlas.LinearGroups.PSLOrderChecks
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-! # The projective transvection subgroups and higher-dimensional simplicity -/

namespace Atlas
open Matrix Matrix.SpecialLinearGroup MulAction
open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

/-- The rank-one transvection x ↦ x + φ(x)v, with φ(v)=0. -/
noncomputable def lineTransvection (v : ι → F) (φ : Module.Dual F (ι → F)) (hφ : φ v = 0) :
    SpecialLinearGroup ι F :=
  ⟨LinearMap.toMatrix' (LinearMap.transvection φ v), by simp [hφ]⟩

theorem lineTransvection_apply (v : ι → F) (φ : Module.Dual F (ι → F)) (hφ : φ v = 0)
    (x : ι → F) : lineTransvection v φ hφ • x = x + φ x • v := by
  change LinearMap.toMatrix' (LinearMap.transvection φ v) *ᵥ x = _
  rw [LinearMap.toMatrix'_mulVec, LinearMap.transvection.apply]

theorem lineTransvection_mem (v : ι → F) (φ : Module.Dual F (ι → F)) (hφ : φ v = 0) :
    lineTransvection v φ hφ ∈ lineStab (Submodule.span F {v}) := by
  intro w
  rw [lineTransvection_apply]
  exact Submodule.mem_span_singleton.mpr ⟨φ w, by abel⟩

theorem lineTransvection_mul (v : ι → F) (φ ψ : Module.Dual F (ι → F))
    (hφ : φ v = 0) (hψ : ψ v = 0) :
    lineTransvection v φ hφ * lineTransvection v ψ hψ =
      lineTransvection v (φ + ψ) (by simp [hφ, hψ]) := by
  apply Subtype.ext
  apply Matrix.ext_iff_smul.mpr
  intro w
  change (lineTransvection v φ hφ * lineTransvection v ψ hψ) • w = _
  rw [mul_smul, lineTransvection_apply, lineTransvection_apply]
  change _ = lineTransvection v (φ + ψ) _ • w
  simp [lineTransvection_apply, map_add, map_smul, hφ, add_smul]
  abel

theorem lineTransvection_zero (v : ι → F) : lineTransvection v 0 (by simp) = 1 := by
  apply Subtype.ext
  apply Matrix.ext_iff_smul.mpr
  intro w
  change lineTransvection v 0 _ • w = (1 : SpecialLinearGroup ι F) • w
  simp [lineTransvection_apply]

theorem lineTransvection_inv (v : ι → F) (φ : Module.Dual F (ι → F)) (hφ : φ v = 0) :
    (lineTransvection v φ hφ)⁻¹ = lineTransvection v (-φ) (by simp [hφ]) := by
  apply inv_eq_of_mul_eq_one_right
  rw [lineTransvection_mul]
  simpa using lineTransvection_zero v

theorem lineTransvection_det (v : ι → F) (φ : Module.Dual F (ι → F)) (hφ : φ v = 0) :
    Matrix.det (lineTransvection v φ hφ : Matrix ι ι F) = 1 :=
  (lineTransvection v φ hφ).prop

theorem lineTransvection_conjugate (g : SpecialLinearGroup ι F) (v : ι → F)
    (φ : Module.Dual F (ι → F)) (hφ : φ v = 0) :
    g * lineTransvection v φ hφ * g⁻¹ =
      lineTransvection (g • v) (φ.comp (g⁻¹).toLin'.toLinearMap)
        (by change φ (g⁻¹ • g • v) = 0; simpa using hφ) := by
  apply Subtype.ext
  apply Matrix.ext_iff_smul.mpr
  intro w
  change (g * lineTransvection v φ hφ * g⁻¹) • w = _
  rw [mul_smul, mul_smul, lineTransvection_apply]
  change _ = lineTransvection (g • v) (φ.comp (g⁻¹).toLin'.toLinearMap) _ • w
  rw [lineTransvection_apply]
  simp [smul_add, smul_comm]
  rfl

theorem lineTransvections_abelian (p : ℙ F (ι → F)) :
    IsMulCommutative (lineStab p.submodule) := by
  rw [← Projectivization.mk_rep p, Projectivization.submodule_mk]
  exact lineStab_isMulCommutative_of_span p.rep p.rep_nonzero

theorem lineTransvections_fix_vectors (p : ℙ F (ι → F)) (g : SpecialLinearGroup ι F)
    (hg : g ∈ lineStab p.submodule) (v : ι → F) (hv : v ∈ p.submodule) : g • v = v := by
  rw [← Projectivization.mk_rep p, Projectivization.submodule_mk] at hg hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [smul_comm, lineStab_fix_of_span p.rep p.rep_nonzero g hg]

/-- The intrinsic rank-one description, including pointwise fixation of the line. -/
theorem lineTransvections_intrinsic (p : ℙ F (ι → F)) (g : SpecialLinearGroup ι F) :
    g ∈ lineStab p.submodule ↔
      (∀ w : ι → F, g • w - w ∈ p.submodule) ∧
        (∀ v ∈ p.submodule, g • v = v) :=
  ⟨fun hg ↦ ⟨hg, lineTransvections_fix_vectors p g hg⟩, fun h ↦ h.1⟩

theorem lineTransvections_fix (p : ℙ F (ι → F)) (g : SpecialLinearGroup ι F)
    (hg : g ∈ lineStab p.submodule) : g • p = p := by
  have h := lineStab_fix_of_span p.rep p.rep_nonzero g
  rw [← Projectivization.submodule_mk (K := F) p.rep p.rep_nonzero,
    Projectivization.mk_rep] at h
  rw [← Projectivization.mk_rep p, Projectivization.smul_mk]
  rw [Projectivization.mk_eq_mk_iff']
  exact ⟨1, by simpa using (h hg).symm⟩

theorem lineTransvections_le_stabilizer (p : ℙ F (ι → F)) :
    lineStab p.submodule ≤ stabilizer (SpecialLinearGroup ι F) p :=
  fun g hg ↦ lineTransvections_fix p g hg

theorem lineTransvections_conj (g : SpecialLinearGroup ι F) (p : ℙ F (ι → F)) :
    lineStab (g • p).submodule = MulAut.conj g • lineStab p.submodule := by
  rw [PSL.smul_submodule, lineStab_smul]

theorem lineTransvections_normal (p : ℙ F (ι → F)) :
    ((lineStab p.submodule).subgroupOf (stabilizer (SpecialLinearGroup ι F) p)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (lineTransvections_le_stabilizer p)).mpr
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg a ha
  have hc : MulAut.conj g • lineStab p.submodule = lineStab p.submodule := by
    rw [← lineTransvections_conj, mem_stabilizer_iff.mp hg]
  rw [← hc]
  exact ⟨a, ha, rfl⟩

theorem projectiveTransvections_abelian (p : ℙ F (ι → F)) :
    IsMulCommutative (PSL.iwasawaT p) := by
  let := lineTransvections_abelian p
  exact Subgroup.map_isMulCommutative _ _

theorem projectiveTransvections_conj (g : ProjectiveSpecialLinearGroup ι F)
    (p : ℙ F (ι → F)) : PSL.iwasawaT (g • p) = MulAut.conj g • PSL.iwasawaT p := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk]
  change Subgroup.map _ _ = _
  rw [lineTransvections_conj, PSL.iwasawaT_map_conj]

theorem projectiveTransvections_le_stabilizer (p : ℙ F (ι → F)) :
    PSL.iwasawaT p ≤ stabilizer (ProjectiveSpecialLinearGroup ι F) p := by
  rintro _ ⟨g, hg, rfl⟩
  exact lineTransvections_fix p g hg

theorem projectiveTransvections_normal (p : ℙ F (ι → F)) :
    ((PSL.iwasawaT p).subgroupOf (stabilizer (ProjectiveSpecialLinearGroup ι F) p)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (projectiveTransvections_le_stabilizer p)).mpr
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg a ha
  have hc : MulAut.conj g • PSL.iwasawaT p = PSL.iwasawaT p := by
    rw [← projectiveTransvections_conj, mem_stabilizer_iff.mp hg]
  rw [← hc]
  exact ⟨a, ha, rfl⟩

theorem lineTransvections_generate [Nontrivial ι] :
    (⨆ p : ℙ F (ι → F), lineStab p.submodule) = ⊤ := by
  apply top_unique
  intro g _
  apply sl_elementary_induction (fun g ↦ g ∈ ⨆ p : ℙ F (ι → F), lineStab p.submodule) _
    (fun _ _ ↦ Subgroup.mul_mem _) g
  intro i j hij a
  let p := Projectivization.mk F (Pi.single i (1 : F) : ι → F)
    (Pi.single_ne_zero_iff.mpr one_ne_zero)
  exact (le_iSup (fun p : ℙ F (ι → F) ↦ lineStab p.submodule) p)
    (SL2Gen.transvection_mem_lineStab hij a)

theorem projectiveTransvections_generate [Nontrivial ι] :
    iSup (PSL.iwasawaT (F := F) (ι := ι)) = ⊤ := by
  have h : iSup (PSL.iwasawaT (F := F) (ι := ι)) =
      Subgroup.map (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup ι F)))
        (⨆ p : ℙ F (ι → F), lineStab p.submodule) := by
    rw [Subgroup.map_iSup]
  rw [h, lineTransvections_generate]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem projectiveTransvections_conjugates_generate [Nontrivial ι] (p : ℙ F (ι → F)) :
    (⨆ g : ProjectiveSpecialLinearGroup ι F, MulAut.conj g • PSL.iwasawaT p) = ⊤ := by
  apply top_unique
  apply (projectiveTransvections_generate (ι := ι) (F := F)).symm.le.trans
  refine iSup_le (fun (q : ℙ F (ι → F)) ↦ ?_)
  obtain ⟨g, rfl⟩ := exists_smul_eq (ProjectiveSpecialLinearGroup ι F) p q
  rw [projectiveTransvections_conj]
  exact le_iSup (fun g : ProjectiveSpecialLinearGroup ι F ↦
    MulAut.conj g • PSL.iwasawaT p) g

noncomputable def pslIwasawa [Nontrivial ι] :
    IwasawaStructure (ProjectiveSpecialLinearGroup ι F) (ℙ F (ι → F)) where
  T := PSL.iwasawaT
  is_comm := projectiveTransvections_abelian
  is_conj := projectiveTransvections_conj
  is_generator := projectiveTransvections_generate

theorem psl_nontrivial [Nontrivial ι] : Nontrivial (ProjectiveSpecialLinearGroup ι F) :=
  inferInstance

theorem psl_simple_high_rank (n : ℕ) (hn : 3 ≤ n) : IsSimpleGroup (PSL(n, F)) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let := psl_perfect (F := F) n hn
  exact IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top pslIwasawa
    (psl_faithful (ι := Fin n) (F := F))

theorem psl_nonabelian_high_rank (n : ℕ) (hn : 3 ≤ n) : ¬ IsMulCommutative (PSL(n, F)) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let := psl_perfect (F := F) n hn
  exact Group.IsPerfect.not_isMulCommutative _

end Atlas
