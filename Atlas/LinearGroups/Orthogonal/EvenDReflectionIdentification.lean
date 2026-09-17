import Atlas.LinearGroups.Orthogonal.ElementaryTransitivityAllChar
import Atlas.LinearGroups.Orthogonal.DicksonElementaryD
import Atlas.LinearGroups.Orthogonal.ElementaryNormal
import Mathlib.FieldTheory.Perfect

/-! # In characteristic two the actual even-reflection subgroup is elementary -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [CharP F 2] [PerfectRing F 2]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (H : WittTwoFrame Q) (hQ : Q.polarBilin.Nondegenerate)

include H hQ in
theorem elementary_transport_equal_value_char_two (a b : V) (ha : Q a ≠ 0)
    (hv : Q a = Q b) :
    ∃ g : isometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val a = b := by
  by_cases hb : b ∈ Submodule.span F {a}
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
    have he : c^2 = 1 := by
      have hh : Q a = c^2 * Q a := by
        calc
          Q a = Q b := hv
          _ = c^2 * Q a := by rw [← hc, Q.map_smul, smul_eq_mul, pow_two]
      exact mul_right_cancel₀ ha (by simpa only [one_mul] using hh.symm)
    have hc1 : c = 1 := by
      rcases sq_eq_one_iff.mp he with he | he
      · exact he
      · simpa only [CharTwo.neg_eq] using he
    refine ⟨1, (elementarySubgroup Q).one_mem, ?_⟩
    change a = b
    simpa only [hc1, one_smul] using hc
  · apply elementary_transport_independent_all_char Q H hQ a b _ hb hv
    intro he
    exact ha (he ▸ Q.map_zero)

include H hQ in
theorem even_reflection_pair_mem_elementary (a b : V) (ha : Q a ≠ 0) (hb : Q b ≠ 0) :
    reflectionElement Q a ha * reflectionElement Q b hb ∈ elementarySubgroup Q := by
  let c := (frobeniusEquiv F 2).symm (Q a / Q b)
  have hc : c^2 = Q a / Q b := (frobeniusEquiv F 2).apply_symm_apply _
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at hc
    exact (div_ne_zero ha hb) hc.symm
  have hval : Q (c • b) = Q a := by
    rw [Q.map_smul, smul_eq_mul, ← pow_two, hc, div_mul_cancel₀ _ hb]
  obtain ⟨g, hg, hga⟩ := elementary_transport_equal_value_char_two Q H hQ a (c • b) ha hval.symm
  let p := QuotientGroup.mk' (elementarySubgroup Q)
  have hgp : p g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  have he := congrArg p (reflectionElement_conj Q g a ha)
  rw [map_mul, map_mul, map_inv, hgp, one_mul, inv_one, mul_one] at he
  have hr : p (reflectionElement Q a ha) = p (reflectionElement Q b hb) := by
    have hcb : Q (c • b) ≠ 0 := by rw [hval]; exact ha
    have heq : reflectionElement Q (g.val a) (by rw [hga, hval]; exact ha) =
        reflectionElement Q (c • b) hcb := by congr 1
    rw [heq, reflectionElement_smul Q b hb c hc0] at he
    exact he
  apply (QuotientGroup.eq_one_iff _).mp
  change p (reflectionElement Q a ha * reflectionElement Q b hb) = 1
  rw [map_mul, hr, ← map_mul, ← pow_two, reflectionElement_square, map_one]

include H hQ in
theorem evenReflection_le_elementary_char_two : evenReflectionSubgroup Q ≤ elementarySubgroup Q := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨a,b,ha,hb,rfl⟩
  exact even_reflection_pair_mem_elementary Q H hQ a b ha hb

theorem evenReflectionD_eq_elementary (n : ℕ) :
    evenReflectionSubgroup (formD (n + 3) F) = elementarySubgroup (formD (n + 3) F) :=
  le_antisymm (evenReflection_le_elementary_char_two _ (wittTwoFrameD (n + 1))
    polarD_nondegenerate) (elementaryD_le_evenReflections_stable n)
end Atlas.Orthogonal
