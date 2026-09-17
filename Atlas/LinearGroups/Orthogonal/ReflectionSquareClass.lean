import Atlas.LinearGroups.Orthogonal.ElementaryQuotient
import Atlas.Algebra.SquareClasses

/-! # Reflection images depend only on their quadratic square class -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (H : WittTwoFrame Q)
  (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

include H hQ h2 in
theorem elementaryProjection_reflection_squareClass (a b : V) (ha : Q a ≠ 0) (hb : Q b ≠ 0)
    (hclass : Atlas.squareClass F (Units.mk0 (Q a) ha) = Atlas.squareClass F (Units.mk0 (Q b) hb)) :
    elementaryProjection Q (reflectionElement Q a ha) =
      elementaryProjection Q (reflectionElement Q b hb) := by
  have hm : Units.mk0 (Q a) ha / Units.mk0 (Q b) hb ∈ Atlas.squareUnits F :=
    QuotientGroup.eq_iff_div_mem.mp hclass
  obtain ⟨c, hc⟩ := hm
  change c^2 = Units.mk0 (Q a) ha / Units.mk0 (Q b) hb at hc
  have hv := congrArg Units.val hc
  simp only [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, Units.val_mk0] at hv
  change c.val^2 = Q a / Q b at hv
  have hv' : Q (c.val • b) = Q a := by
    rw [Q.map_smul, smul_eq_mul]
    rw [← pow_two]
    rw [hv, div_mul_cancel₀ _ hb]
  have hcb : Q (c.val • b) ≠ 0 := ne_of_eq_of_ne hv' ha
  have he := elementaryProjection_reflection_equal_value Q H hQ h2 a (c.val • b) ha hcb hv'.symm
  rwa [reflectionElement_smul Q b hb c.val c.ne_zero] at he

end Atlas.Orthogonal
