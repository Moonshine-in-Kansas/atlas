import Atlas.LinearGroups.Orthogonal.ElementaryQuotient
import Atlas.LinearGroups.Orthogonal.PairOrbit

/-! # Correcting full pair transport inside the elementary subgroup -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (H : WittTwoFrame Q)
  (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

include H hQ h2 in
/-- A pair stabilizer represents every elementary quotient coset if its complement
represents all nonzero field values. This uses actual reflections in that complement. -/
theorem pairStabilizer_projection_surjective (e f : V)
    (hrep : ∀ c : F, c ≠ 0 → ∃ a : complement Q e f, Q a.val = c) :
    Function.Surjective ((elementaryProjection Q).comp (pairStabilizer Q e f).subtype) := by
  let π := (elementaryProjection Q).comp (pairStabilizer Q e f).subtype
  have hr : reflectionSubgroup Q ≤ π.range.comap (elementaryProjection Q) := by
    apply (Subgroup.closure_le _).mpr
    rintro r ⟨a, ha, rfl⟩
    obtain ⟨b, hb⟩ := hrep (Q a) ha
    have hbn : Q b.val ≠ 0 := ne_of_eq_of_ne hb ha
    have hfix : reflectionElement Q b.val hbn ∈ pairStabilizer Q e f := by
      constructor
      · change reflectionLinear Q b.val hbn e = e
        rw [reflectionLinear_apply, (polar_swap Q e b.val).trans b.prop.1,
          mul_zero, zero_smul, sub_zero]
      · change reflectionLinear Q b.val hbn f = f
        rw [reflectionLinear_apply, (polar_swap Q f b.val).trans b.prop.2,
          mul_zero, zero_smul, sub_zero]
    refine ⟨⟨reflectionElement Q b.val hbn, hfix⟩, ?_⟩
    exact elementaryProjection_reflection_equal_value Q H hQ h2 b.val a hbn ha hb
  rw [reflectionSubgroup_eq_top Q hQ h2] at hr
  intro z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (elementarySubgroup Q) z
  exact hr (Subgroup.mem_top g)

include H hQ h2 in
/-- Full pair transport can be corrected by a source-pair fixer to lie in E. -/
theorem elementary_transport_hyperbolic_pair
    (hrad : Q.radical = ⊥) (e f u v : V)
    (he : Q e = 0) (hf : Q f = 0) (hu : Q u = 0) (hv : Q v = 0)
    (hef : Q.polarBilin e f = 1) (huv : Q.polarBilin u v = 1)
    (hrep : ∀ c : F, c ≠ 0 → ∃ a : complement Q e f, Q a.val = c) :
    ∃ g : isometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val e = u ∧ g.val f = v := by
  obtain ⟨g, hge, hgf⟩ := exists_isometry_hyperbolic_pair Q hrad e f u v he hf hu hv hef huv
  let t := (isometryCarrierEquiv Q).symm g
  obtain ⟨k, hk⟩ := pairStabilizer_projection_surjective Q H hQ h2 e f hrep
    ((elementaryProjection Q t)⁻¹)
  have ht : t * k.val ∈ elementarySubgroup Q := by
    apply (QuotientGroup.eq_one_iff (t*k.val)).mp
    change elementaryProjection Q (t*k.val) = 1
    rw [map_mul]
    change elementaryProjection Q t *
      ((elementaryProjection Q).comp (pairStabilizer Q e f).subtype) k = 1
    rw [hk, mul_inv_cancel]
  refine ⟨t*k.val, ht, ?_, ?_⟩
  · change t.val (k.val.val e) = u
    rw [k.prop.1]
    exact hge
  · change t.val (k.val.val f) = v
    rw [k.prop.2]
    exact hgf
end Atlas.Orthogonal
