import Atlas.LinearGroups.ReeF4.LongRootStarCompatibility
import Atlas.Algebra.Albert.TraceZeroStabilizerEquiv

/-! The full partial-product stabilizer of the explicit candidate. Its comparison
with the intended Ree construction is still subject to the remaining generator
and geometry gates; no order or simplicity result is asserted here. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem starDomain_polynomialStabilizer_iff
    (g : traceZeroPolynomialStabilizer (F := F)) (u v : TraceZero F) :
    StarDomain (g.val u) (g.val v) ↔ StarDomain u v := by
  have hp := traceZeroPolar_of_quadratic g.val (traceZeroStabilizer_quadratic g) u v
  have hc := traceZeroCross_of_forms g.val (traceZeroStabilizer_quadratic g)
    (traceZeroStabilizer_cubic g) u v
  change (_ = 0 ∧ _ = 0) ↔ (_ = 0 ∧ _ = 0)
  rw [hp, hc]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨h1, g.val.injective (h2.trans (g.val.map_zero).symm)⟩
  · rintro ⟨h1,h2⟩
    exact ⟨h1, by rw [h2, _root_.map_zero]⟩

def PreservesCandidatePartial (σ : F →+* F)
    (g : traceZeroPolynomialStabilizer (F := F)) : Prop :=
  ∀ (u v : TraceZero F) (h : StarDomain u v),
    proposedPartialProduct σ (g.val u) (g.val v)
      ((starDomain_polynomialStabilizer_iff g u v).mpr h) =
      g.val (proposedPartialProduct σ u v h)

def candidatePartialStabilizer (σ : F →+* F) :
    Subgroup (traceZeroPolynomialStabilizer (F := F)) where
  carrier := PreservesCandidatePartial σ
  one_mem' := by intro u v h; rfl
  mul_mem' := by
    intro g k hg hk u v h
    change proposedPartialProduct σ (g.val (k.val u)) (g.val (k.val v)) _ =
      g.val (k.val (proposedPartialProduct σ u v h))
    rw [hg _ _ ((starDomain_polynomialStabilizer_iff k u v).mpr h), hk u v h]
  inv_mem' := by
    intro g hg u v h
    apply g.val.injective
    have hdom := (starDomain_polynomialStabilizer_iff (g⁻¹) u v).mpr h
    have he := hg ((g⁻¹).val u) ((g⁻¹).val v) hdom
    change proposedPartialProduct σ (g.val (g.val.symm u)) (g.val (g.val.symm v)) _ =
      g.val (proposedPartialProduct σ (g.val.symm u) (g.val.symm v) _) at he
    change g.val (proposedPartialProduct σ (g.val.symm u) (g.val.symm v) _) =
      g.val (g.val.symm (proposedPartialProduct σ u v h))
    simpa only [LinearEquiv.apply_symm_apply] using he.symm

/-- The actual inclusion into the retained full Albert polynomial-and-unit stabilizer. -/
def candidateAlbertEmbedding (σ : F →+* F) : candidatePartialStabilizer σ →*
    polynomialStabilizer (F := F) :=
  traceZeroStabilizerEquiv.toMonoidHom.comp (candidatePartialStabilizer σ).subtype

theorem candidateAlbertEmbedding_injective (σ : F →+* F) :
    Function.Injective (candidateAlbertEmbedding σ) :=
  traceZeroStabilizerEquiv.injective.comp Subtype.val_injective

theorem longRoot_mem_candidatePartialStabilizer (σ : F →+* F) :
    (⟨longRootEquiv, longRootEquiv_mem_polynomialStabilizer⟩ :
      traceZeroPolynomialStabilizer (F := F)) ∈ candidatePartialStabilizer σ := by
  intro u v h
  exact proposedPartialProduct_longRoot σ u v h

end Atlas.ReeF4
