import Atlas.LinearGroups.Orthogonal.Minus.OrderBase
import Atlas.LinearGroups.Orthogonal.ElementaryReflectionGeneration

/-! Reflection generation of the genuine anisotropic norm plane, in every characteristic. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic Atlas.Quadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem plane_reflection_apply (hdeg : Module.finrank F K = 2) (a : K)
    (ha : normForm hdeg a ≠ 0) (z : K) :
    (reflectionElement (normForm hdeg) a ha).val z =
      -(a / conjugation F K a) * conjugation F K z := by
  change reflectionLinear (normForm hdeg) a ha z = _
  rw [reflectionLinear_apply, normForm_polar, normForm_apply, Algebra.smul_def,
    map_mul, map_inv₀, norm_formula hdeg, trace_formula hdeg, map_mul,
    conjugation_conjugation hdeg]
  have ha0 : a ≠ 0 := fun h => ha ((normForm_eq_zero_iff hdeg a).mpr h)
  have has : conjugation F K a ≠ 0 := (map_ne_zero _).mpr ha0
  field_simp
  ring

theorem planeConjugation_mem_reflections (hdeg : Module.finrank F K = 2) :
    planeConjugation hdeg ∈ reflectionSubgroup (normForm hdeg) := by
  obtain ⟨a,ha,ht⟩ := exists_nonzero_trace_zero hdeg
  have hqa : normForm hdeg a ≠ 0 := fun h => ha ((normForm_eq_zero_iff hdeg a).mp h)
  have hs : conjugation F K a = -a := eq_neg_of_add_eq_zero_right ht
  have he : reflectionElement (normForm hdeg) a hqa = planeConjugation hdeg := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    rw [plane_reflection_apply, hs, div_neg, neg_neg, div_self ha, one_mul]
    rfl
  rw [← he]
  exact reflectionElement_mem _ _ _

theorem plane_reflectionSubgroup_eq_top (hdeg : Module.finrank F K = 2) :
    reflectionSubgroup (normForm hdeg) = ⊤ := by
  apply top_unique
  intro g _
  by_cases hg : g.val 1 = 1
  · rcases plane_fix_one_classification hdeg g hg with he | he
    · rw [he]; exact Subgroup.one_mem _
    · rw [he]; exact planeConjugation_mem_reflections hdeg
  · have hn : normForm hdeg (g.val 1 - 1) ≠ 0 := by
      intro h
      exact hg (sub_eq_zero.mp ((normForm_eq_zero_iff hdeg _).mp h))
    let r := reflectionElement (normForm hdeg) (g.val 1 - 1) hn
    have hr : r ∈ reflectionSubgroup (normForm hdeg) := reflectionElement_mem _ _ _
    have hfix : (r*g).val 1 = 1 :=
      reflection_equal_value (normForm hdeg) (g.val 1) 1 (g.prop 1) hn
    have hrg : r*g ∈ reflectionSubgroup (normForm hdeg) := by
      rcases plane_fix_one_classification hdeg (r*g) hfix with he | he
      · rw [he]; exact Subgroup.one_mem _
      · rw [he]; exact planeConjugation_mem_reflections hdeg
    simpa only [inv_mul_cancel_left] using
      (reflectionSubgroup (normForm hdeg)).mul_mem
        ((reflectionSubgroup (normForm hdeg)).inv_mem hr) hrg

/-- The actual internal zero-rank group supplies the base of joint generation. -/
theorem zeroRank_elementaryReflection_eq_top (hdeg : Module.finrank F K = 2) :
    elementaryReflectionSubgroup (form hdeg 0) = ⊤ := by
  apply top_unique
  intro g _
  have hg : zeroRankGroupEquiv hdeg g ∈ reflectionSubgroup (normForm hdeg) := by
    rw [plane_reflectionSubgroup_eq_top hdeg]
    trivial
  have h := isometryTransport_mem_elementaryReflection (zeroRankIsometry hdeg).symm
    (zeroRankGroupEquiv hdeg g) ((show reflectionSubgroup (normForm hdeg) ≤ elementaryReflectionSubgroup (normForm hdeg) from le_sup_right) hg)
  have he : isometryGroupTransport (zeroRankIsometry hdeg).symm
      (zeroRankGroupEquiv hdeg g) = g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change (zeroRankIsometry hdeg).symm
      ((zeroRankIsometry hdeg) (g.val ((zeroRankIsometry hdeg).symm
        ((zeroRankIsometry hdeg) x)))) = g.val x
    rw [QuadraticMap.IsometryEquiv.symm_apply_apply,
      QuadraticMap.IsometryEquiv.symm_apply_apply]
  rwa [he] at h

end Atlas.Orthogonal.Minus

