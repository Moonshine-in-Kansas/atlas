import Atlas.LinearGroups.Orthogonal.ElementaryTorus

/-! # Two sign tori compensate their spinor values -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)
variable (e f : V) (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

theorem hyperbolicTorus_determinant (c : F) (hc : c ≠ 0) :
    determinant Q (hyperbolicTorus Q e f he hf hef c hc) = 1 := by
  simp only [hyperbolicTorus, hyperbolicReflection, map_mul, reflectionElement_determinant,
    neg_mul_neg, one_mul]

theorem hyperbolicTorus_spinorNorm (c : F) (hc : c ≠ 0) :
    spinorNorm Q hQ h2 (hyperbolicTorus Q e f he hf hef c hc) =
      Atlas.squareClass F (Units.mk0 c hc) := by
  simp only [hyperbolicTorus, hyperbolicReflection, map_mul, spinorNorm_reflection]
  have h₁ : Units.mk0 (Q (e+(1 : F) • f))
      (ne_of_eq_of_ne (hyperbolic_reflection_norm Q e f he hf hef 1) one_ne_zero) = (1 : Fˣ) :=
    Units.ext (hyperbolic_reflection_norm Q e f he hf hef 1)
  have h₂ : Units.mk0 (Q (e+c • f))
      (ne_of_eq_of_ne (hyperbolic_reflection_norm Q e f he hf hef c) hc) = Units.mk0 c hc :=
    Units.ext (hyperbolic_reflection_norm Q e f he hf hef c)
  rw [h₁, h₂, map_one, one_mul]

variable (a b : V) (ha : Q a = 0) (hb : Q b = 0) (hab : Q.polarBilin a b = 1)

def compensatedTorus : isometrySubgroup Q :=
  hyperbolicTorus Q e f he hf hef (-1) (neg_ne_zero.mpr one_ne_zero) *
    hyperbolicTorus Q a b ha hb hab (-1) (neg_ne_zero.mpr one_ne_zero)

include hQ h2 in
theorem compensatedTorus_mem_elementary [Finite F] (H : WittTwoFrame Q) :
    compensatedTorus Q e f he hf hef a b ha hb hab ∈ elementarySubgroup Q := by
  apply (elementary_eq_intrinsicKernel Q H hQ h2).ge
  constructor
  · change determinant Q (compensatedTorus Q e f he hf hef a b ha hb hab) = 1
    simp only [compensatedTorus, map_mul, hyperbolicTorus_determinant, one_mul]
  · change spinorNorm Q hQ h2 (compensatedTorus Q e f he hf hef a b ha hb hab) = 1
    rw [compensatedTorus, map_mul, hyperbolicTorus_spinorNorm, hyperbolicTorus_spinorNorm,
      ← map_mul, ← pow_two, Atlas.squareClass_square]

theorem compensatedTorus_e (hea : Q.polarBilin e a = 0) (heb : Q.polarBilin e b = 0) :
    (compensatedTorus Q e f he hf hef a b ha hb hab).val e = -e := by
  have ht := hyperbolicTorus_perp Q a b ha hb hab (-1) (neg_ne_zero.mpr one_ne_zero)
    (⟨e, hea, heb⟩ : complement Q a b)
  change (hyperbolicTorus Q e f he hf hef (-1) (neg_ne_zero.mpr one_ne_zero)).val
    ((hyperbolicTorus Q a b ha hb hab (-1) (neg_ne_zero.mpr one_ne_zero)).val e) = -e
  rw [ht, hyperbolicTorus_e, neg_one_smul]

theorem compensatedTorus_perp (v : complement Q e f)
    (hva : Q.polarBilin v.val a = 0) (hvb : Q.polarBilin v.val b = 0) :
    (compensatedTorus Q e f he hf hef a b ha hb hab).val v.val = v.val := by
  have ht := hyperbolicTorus_perp Q a b ha hb hab (-1) (neg_ne_zero.mpr one_ne_zero)
    (⟨v.val, hva, hvb⟩ : complement Q a b)
  change (hyperbolicTorus Q e f he hf hef (-1) (neg_ne_zero.mpr one_ne_zero)).val
    ((hyperbolicTorus Q a b ha hb hab (-1) (neg_ne_zero.mpr one_ne_zero)).val v.val) = v.val
  rw [ht, hyperbolicTorus_perp]

end Atlas.Orthogonal
