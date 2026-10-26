import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Tactic

/-! Canonical cubic Frobenius, trace and norm over actual finite-field extensions. -/
noncomputable section
namespace Atlas.FiniteCubic
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def sigma : K ≃ₐ[F] K :=
  let := Fintype.ofFinite F
  FiniteField.frobeniusAlgEquivOfAlgebraic F K

theorem sigma_apply (x : K) : sigma F K x=x^Nat.card F := by
  simp [sigma,← Nat.card_eq_fintype_card]

@[simp] theorem sigma_base (x : F) : sigma F K (algebraMap F K x)=algebraMap F K x :=
  (sigma F K).commutes x

variable {F K}
theorem card_extension (hdeg : Module.finrank F K=3) : Nat.card K=Nat.card F^3 := by
  rw [Module.natCard_eq_pow_finrank (K := F),hdeg]

theorem sigma_cube (hdeg : Module.finrank F K=3) (x : K) :
    sigma F K (sigma F K (sigma F K x))=x := by
  rw [sigma_apply,sigma_apply,sigma_apply,← pow_mul,← pow_mul,
    show Nat.card F*(Nat.card F*Nat.card F)=Nat.card F^3 by ring,← card_extension hdeg]
  let := Fintype.ofFinite K
  simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card x

theorem sigma_order (hdeg : Module.finrank F K=3) : orderOf (sigma F K)=3 := by
  let := Fintype.ofFinite F
  exact (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F K).trans hdeg

theorem sigma_fixed_iff (hdeg : Module.finrank F K=3) (x : K) :
    sigma F K x=x ↔ ∃ a : F, algebraMap F K a=x := by
  constructor
  · intro hx
    apply (IsGalois.mem_range_algebraMap_iff_fixed x).mpr
    intro g
    let := Fintype.ofFinite F
    obtain ⟨i,hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F K).surjective g
    have hb : i.val<3 := hdeg ▸ i.isLt
    rw [← hi]
    change (sigma F K ^ i.val) x=x
    interval_cases h : i.val <;> simp [h,AlgEquiv.mul_apply,pow_succ,hx]
  · rintro ⟨a,rfl⟩
    exact sigma_base F K a

variable (F K)
abbrev trace : K →ₗ[F] F := Algebra.trace F K
abbrev norm : K →* F := Algebra.norm F

theorem trace_surjective : Function.Surjective (trace F K) := Algebra.trace_surjective F K

theorem norm_units_surjective : Function.Surjective (Units.map (norm F K)) :=
  FiniteField.unitsMap_norm_surjective F K

variable {F K}
theorem trace_formula (hdeg : Module.finrank F K=3) (x : K) :
    algebraMap F K (trace F K x)=x+sigma F K x+sigma F K (sigma F K x) := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow,hdeg]
  simp [Finset.sum_range_succ,sigma_apply,pow_mul,pow_two]

theorem norm_formula (hdeg : Module.finrank F K=3) (x : K) :
    algebraMap F K (norm F K x)=x*sigma F K x*sigma F K (sigma F K x) := by
  rw [FiniteField.algebraMap_norm_eq_prod_pow,hdeg]
  simp [Finset.prod_range_succ,sigma_apply,pow_mul,pow_two]

theorem map_sigma {L : Type*} [Field L] [Finite L] [Algebra F L]
    (e : K ≃ₐ[F] L) (x : K) : e (sigma F K x)=sigma F L (e x) := by
  simp only [sigma_apply,map_pow]

theorem extension_exists (F : Type*) [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra F K),
      Module.finrank F K=3 ∧ Nat.card K=Nat.card F^3 := by
  exact ⟨FiniteField.Extension F p 3,inferInstance,inferInstance,inferInstance,
    FiniteField.finrank_extension F p 3,FiniteField.natCard_extension F p 3⟩
end Atlas.FiniteCubic
