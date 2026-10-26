import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic

/-! # The canonical involution of an actual quadratic extension of finite fields

No star instance is installed on the extension field. All maps retain the actual
base algebra structure. The degree-two hypothesis is explicit, not a packaged
assumption about trace, norm, or any group to be constructed later.
-/
noncomputable section
namespace Atlas.FiniteQuadratic
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- The canonical base-cardinality Frobenius, using the existing finite-field API. -/
def conjugation : K ≃ₐ[F] K :=
  let := Fintype.ofFinite F
  FiniteField.frobeniusAlgEquivOfAlgebraic F K

theorem conjugation_apply (x : K) :
    conjugation F K x = x ^ Nat.card F := by
  simp [conjugation, ← Nat.card_eq_fintype_card]

@[simp] theorem conjugation_base (x : F) :
    conjugation F K (algebraMap F K x) = algebraMap F K x :=
  (conjugation F K).commutes x

variable {F K}

theorem card_extension (hdeg : Module.finrank F K = 2) :
    Nat.card K = Nat.card F ^ 2 := by
  rw [Module.natCard_eq_pow_finrank (K := F), hdeg]

theorem conjugation_involutive (hdeg : Module.finrank F K = 2) :
    Function.Involutive (conjugation F K) := by
  intro x
  rw [conjugation_apply, conjugation_apply, ← pow_mul, ← pow_two,
    ← card_extension hdeg]
  let := Fintype.ofFinite K
  simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card x

@[simp] theorem conjugation_conjugation (hdeg : Module.finrank F K = 2) (x : K) :
    conjugation F K (conjugation F K x) = x := conjugation_involutive hdeg x

theorem conjugation_order
 (hdeg : Module.finrank F K = 2) :
    orderOf (conjugation F K) = 2 := by
  let := Fintype.ofFinite F
  exact (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F K).trans hdeg

theorem conjugation_ne_one (hdeg : Module.finrank F K = 2) :
    conjugation F K ≠ 1 := by
  intro h
  have := conjugation_order hdeg
  rw [h, orderOf_one] at this
  omega

/-- Fixed elements are exactly the embedded base field, not just an abstract field
of the same cardinality. -/
theorem conjugation_fixed_iff (hdeg : Module.finrank F K = 2) (x : K) :
    conjugation F K x = x ↔ ∃ a : F, algebraMap F K a = x := by
  constructor
  · intro hx
    apply (IsGalois.mem_range_algebraMap_iff_fixed x).mpr
    intro g
    let := Fintype.ofFinite F
    obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F K).surjective g
    have hi2 : i.val < 2 := hdeg ▸ i.isLt
    have hi01 : i.val = 0 ∨ i.val = 1 := by omega
    rcases hi01 with h | h
    · simpa only [← hi, h, pow_zero] using (show (1 : K ≃ₐ[F] K) x = x from rfl)
    · rw [← hi]
      change (FiniteField.frobeniusAlgEquivOfAlgebraic F K ^ i.val) x = x
      rw [h, pow_one]
      exact hx
  · rintro ⟨a, rfl⟩
    exact conjugation_base F K a

theorem automorphism_eq_one_or_conjugation (hdeg : Module.finrank F K = 2)
    (g : K ≃ₐ[F] K) : g = 1 ∨ g = conjugation F K := by
  let := Fintype.ofFinite F
  obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F K).surjective g
  have hi2 : i.val < 2 := hdeg ▸ i.isLt
  have hi01 : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi01 with h | h
  · left; simpa only [h, pow_zero] using hi.symm
  · right; simpa only [h, pow_one, conjugation] using hi.symm

variable (F K)
/-- Field-theoretic
 trace, with codomain the actual base field. -/
abbrev trace : K →ₗ[F] F := Algebra.trace F K
/-- Field-theoretic norm, with codomain the actual base field. -/
abbrev norm : K →* F := Algebra.norm F

theorem trace_surjective : Function.Surjective (trace F K) := Algebra.trace_surjective F K

omit [Finite F] in
theorem norm_surjective : Function.Surjective (norm F K) := FiniteField.norm_surjective F K

omit [Finite F] in
theorem norm_units_surjective :
    Function.Surjective (Units.map (norm F K)) :=
  FiniteField.unitsMap_norm_surjective F K

variable {F K}
theorem norm_formula (hdeg : Module.finrank F K = 2) (x : K) :
    algebraMap F K (norm F K x) = x * conjugation F K x := by
  rw [FiniteField.algebraMap_norm_eq_pow, card_extension hdeg, conjugation_apply]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have he : (Nat.card F ^ 2 - 1) / (Nat.card F - 1) = Nat.card F + 1 := by
    have h : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
      nlinarith [Nat.sub_add_cancel (show 1 ≤ Nat.card F by omega),
        Nat.sub_add_cancel (show 1 ≤ Nat.card F ^ 2 by nlinarith)]
    rw [h, Nat.mul_div_cancel _ (by omega)]
  rw [he, pow_succ]
  exact mul_comm _ _

theorem trace_formula (hdeg : Module.finrank F K = 2) (x : K) :
    algebraMap F K (trace F K x) = x + conjugation F K x := by
  classical
  have huniv : (Finset.univ : Finset (K ≃ₐ[F] K)) = {1, conjugation F K} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact automorphism_eq_one_or_conjugation hdeg g
  rw [trace_eq_sum_automorphisms, huniv]
  simp [Ne.symm (conjugation_ne_one hdeg)]

/-- Compatibility under an actual base-preserving field isomorphism. -/
theorem map_conjugation {L : Type*} [Field L] [Finite L] [Algebra F L]
    (e : K ≃ₐ[F] L) (x : K) :
    e (conjugation F K x) = conjugation F L (e x) := by
  simp only [conjugation_apply, map_pow]

/-- An actual degree-two extension with its base embedding, provided by mathlib. -/
theorem extension_exists (F : Type*) [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra F K),
      Module.finrank F K = 2 ∧ Nat.card K = Nat.card F ^ 2 := by
  exact ⟨FiniteField.Extension F p 2, inferInstance, inferInstance, inferInstance,
    FiniteField.finrank_extension F p 2, FiniteField.natCard_extension F p 2⟩
end Atlas.FiniteQuadratic
